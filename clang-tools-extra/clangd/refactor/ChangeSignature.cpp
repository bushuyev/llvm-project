//===--- ChangeSignature.cpp - Semantic signature edits ----------*- C++
//-*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "refactor/ChangeSignature.h"
#include "AST.h"
#include "Compiler.h"
#include "Diagnostics.h"
#include "GlobalCompilationDatabase.h"
#include "ParsedAST.h"
#include "Selection.h"
#include "SourceCode.h"
#include "URI.h"
#include "index/Index.h"
#include "support/Cancellation.h"
#include "support/ThreadsafeFS.h"
#include "clang/AST/DeclCXX.h"
#include "clang/AST/ExprCXX.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/AST/TypeLoc.h"
#include "clang/Basic/Diagnostic.h"
#include "clang/Lex/Lexer.h"
#include "clang/Tooling/Core/Replacement.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/ADT/StringMap.h"
#include "llvm/Support/MemoryBuffer.h"
#include <set>

namespace clang::clangd {
namespace {

llvm::Error reject(llvm::Twine Reason) {
  return llvm::createStringError(llvm::inconvertibleErrorCode(), Reason);
}

bool supported(const FunctionDecl &Function) {
  return Function.getDeclName().isIdentifier() && !Function.isVariadic() &&
         !Function.isTemplated() && !Function.isExternC() &&
         !Function.getLocation().isMacroID() &&
         !Function.getASTContext().getSourceManager().isInSystemHeader(
             Function.getLocation()) &&
         !llvm::isa<CXXConstructorDecl, CXXDestructorDecl>(Function);
}

const FunctionDecl *virtualRoot(const FunctionDecl *Function) {
  while (auto *Method = llvm::dyn_cast<CXXMethodDecl>(Function)) {
    if (Method->size_overridden_methods() > 1)
      return nullptr;
    if (Method->size_overridden_methods() == 0)
      break;
    Function = *Method->begin_overridden_methods();
  }
  return Function;
}

struct Parameter {
  std::optional<unsigned> OldIndex;
  std::string Name;
  std::string Type;
  std::optional<std::string> Argument;
};

struct Signature {
  std::string Name;
  std::string ReturnType;
  std::vector<Parameter> Parameters;
};

Signature signatureOf(const FunctionDecl &Function) {
  Signature Signature{
      Function.getNameAsString(), Function.getReturnType().getAsString(), {}};
  for (const ParmVarDecl *Param : Function.parameters())
    Signature.Parameters.push_back(
        {Param->getFunctionScopeIndex(), Param->getNameAsString(),
         Param->getType().getAsString(), std::nullopt});
  return Signature;
}

llvm::json::Value toJSON(const Signature &Signature) {
  llvm::json::Array Parameters;
  for (const Parameter &Param : Signature.Parameters)
    Parameters.push_back(llvm::json::Object{
        {"oldIndex", Param.OldIndex ? llvm::json::Value(*Param.OldIndex)
                                    : llvm::json::Value(nullptr)},
        {"name", Param.Name},
        {"type", Param.Type}});
  return llvm::json::Object{{"name", Signature.Name},
                            {"returnType", Signature.ReturnType},
                            {"parameters", std::move(Parameters)}};
}

llvm::Expected<Signature> parseSignature(llvm::StringRef Answer,
                                         const Signature &Original,
                                         ASTContext &Context) {
  auto Parsed = llvm::json::parse(Answer);
  if (!Parsed)
    return Parsed.takeError();
  const auto *Object = Parsed->getAsObject();
  if (!Object || Object->getString("name") != Original.Name)
    return reject("Use Rename Symbol to change the function name");
  auto ReturnType = Object->getString("returnType");
  const auto *Params = Object->getArray("parameters");
  if (!ReturnType || ReturnType->trim().empty() || !Params)
    return reject("Provide a return type and an ordered parameter list");
  auto SafeType = [](llvm::StringRef Type) {
    return !Type.trim().empty() &&
           Type.find_first_of(";{}()[]#=\n") == llvm::StringRef::npos &&
           !Type.contains("/*") && !Type.contains("//") &&
           (Type.count('<') == Type.count('>')) &&
           (Type.contains('<') || !Type.contains(','));
  };
  if (*ReturnType != Original.ReturnType && !SafeType(*ReturnType))
    return reject("Unsupported return type syntax");
  Signature Result{Original.Name, ReturnType->str(), {}};
  std::set<unsigned> Identities;
  std::set<std::string> Names;
  for (const auto &Entry : *Params) {
    const auto *Param = Entry.getAsObject();
    if (!Param)
      return reject("Each parameter must be an object");
    auto Name = Param->getString("name");
    auto Type = Param->getString("type");
    const auto *Identity = Param->get("oldIndex");
    if (!Name || !Type || !Identity)
      return reject("Each parameter needs an oldIndex, name, and type");
    Parameter P{std::nullopt, Name->str(), Type->str(), std::nullopt};
    if (auto Old = Identity->getAsInteger()) {
      if (*Old < 0 || static_cast<size_t>(*Old) >= Original.Parameters.size() ||
          !Identities.insert(*Old).second)
        return reject("Unknown or repeated parameter identity");
      P.OldIndex = *Old;
    } else if (Identity->getAsNull()) {
      auto Argument = Param->getString("argument");
      if (!Argument || Argument->trim().empty() ||
          Argument->find_first_of(";{}#\n") != llvm::StringRef::npos ||
          Argument->contains("/*") || Argument->contains("//"))
        return reject(
            "Provide one argument expression for every new parameter");
      // Reject a comma that would create two arguments at a call site.
      int Depth = 0;
      for (auto Character : *Argument) {
        if (Character == '(')
          ++Depth;
        else if (Character == ')')
          --Depth;
        if (Depth < 0 || (Depth == 0 && Character == ','))
          return reject("The new argument must be one expression");
      }
      if (Depth != 0)
        return reject("The new argument has unbalanced parentheses");
      P.Argument = Argument->str();
    } else {
      return reject("oldIndex must be an integer or null");
    }
    if (Name->empty()) {
      if (!P.OldIndex || !Original.Parameters[*P.OldIndex].Name.empty())
        return reject("The new parameter needs a name");
    } else if (!(llvm::isAlpha(Name->front()) || Name->front() == '_') ||
               !llvm::all_of(
                   *Name,
                   [](char C) { return llvm::isAlnum(C) || C == '_'; }) ||
               Context.Idents.get(*Name).isKeyword(Context.getLangOpts()) ||
               !Names.insert(P.Name).second) {
      return reject("Use unique ordinary C++ identifiers for parameter names");
    }
    if ((!P.OldIndex || P.Type != Original.Parameters[*P.OldIndex].Type) &&
        !SafeType(P.Type))
      return reject("Unsupported parameter type syntax");
    Result.Parameters.push_back(std::move(P));
  }
  return Result;
}

struct FileChanges {
  std::string Original;
  tooling::Replacements Edits;
};

class Rewrite {
public:
  Rewrite(const Signature &Original, const Signature &Requested,
          const SymbolID &RootID)
      : Original(Original), Requested(Requested), RootID(RootID) {
    std::vector<unsigned> Retained;
    for (const auto &Param : Requested.Parameters)
      if (Param.OldIndex)
        Retained.push_back(*Param.OldIndex);
    Reorder = !llvm::is_sorted(Retained);
    Structural = Retained.size() != Original.Parameters.size() ||
                 Requested.Parameters.size() != Original.Parameters.size() ||
                 Reorder;
    for (const auto &Param : Requested.Parameters)
      if (Param.OldIndex &&
          Param.Type != Original.Parameters[*Param.OldIndex].Type)
        TypeChange = true;
    TypeChange |= Original.ReturnType != Requested.ReturnType;
  }

  bool matches(const FunctionDecl &Function) const {
    if (!Function.getIdentifier() || Function.getName() != Original.Name)
      return false;
    const FunctionDecl *Root = virtualRoot(&Function);
    if (Root)
      return getSymbolID(Root->getCanonicalDecl()) == RootID;
    llvm::SmallPtrSet<const FunctionDecl *, 8> Visited;
    llvm::SmallVector<const FunctionDecl *> Pending{&Function};
    while (!Pending.empty()) {
      const auto *Declaration = Pending.pop_back_val();
      if (!Visited.insert(Declaration).second)
        continue;
      if (getSymbolID(Declaration->getCanonicalDecl()) == RootID)
        return true;
      if (auto *Method = llvm::dyn_cast<CXXMethodDecl>(Declaration))
        Pending.append(Method->begin_overridden_methods(),
                       Method->end_overridden_methods());
    }
    return false;
  }

  llvm::Expected<llvm::StringRef> text(ASTContext &Context, SourceRange Range) {
    if (!Range.isValid() || Range.getBegin().isMacroID() ||
        Range.getEnd().isMacroID())
      return reject("Cannot rewrite source generated by a macro");
    bool Invalid = false;
    llvm::StringRef Text = Lexer::getSourceText(
        CharSourceRange::getTokenRange(Range), Context.getSourceManager(),
        Context.getLangOpts(), &Invalid);
    if (Invalid)
      return reject("Cannot recover a contiguous spelling range");
    return Text;
  }

  llvm::Error edit(ASTContext &Context, CharSourceRange Range,
                   llvm::StringRef NewText) {
    const SourceManager &SM = Context.getSourceManager();
    if (Range.getBegin().isMacroID() || Range.getEnd().isMacroID())
      return reject("Cannot edit macro-generated source");
    auto FileRange = Lexer::makeFileCharRange(Range, SM, Context.getLangOpts());
    if (FileRange.isInvalid() || SM.isInSystemHeader(FileRange.getBegin()))
      return reject("The transformation requires editing unavailable source");
    FileID File = SM.getFileID(FileRange.getBegin());
    auto Entry = SM.getFileEntryRefForID(File);
    if (!Entry)
      return reject("Could not identify an edited file");
    auto Path = getCanonicalPath(*Entry, SM.getFileManager());
    if (!Path)
      return reject("Could not determine the path of an edited file");
    bool Invalid = false;
    llvm::StringRef Buffer = SM.getBufferData(File, &Invalid);
    if (Invalid)
      return reject("Could not read the original source of an edited file");
    auto [Iterator, Inserted] = Changes.try_emplace(*Path);
    FileChanges &ChangesForFile = Iterator->second;
    if (Inserted)
      ChangesForFile.Original = Buffer.str();
    else if (ChangesForFile.Original != Buffer)
      return reject("The file differs between translation units");
    unsigned Begin = SM.getFileOffset(FileRange.getBegin());
    unsigned End = SM.getFileOffset(FileRange.getEnd());
    SeenFiles.insert(*Path);
    if (Buffer.slice(Begin, End) == NewText)
      return llvm::Error::success();
    if (End < Begin || End > Buffer.size())
      return reject("Invalid replacement range");
    return ChangesForFile.Edits.add(
        tooling::Replacement(*Path, Begin, End - Begin, NewText));
  }

  void note(ASTContext &Context, SourceLocation Location) {
    const SourceManager &SM = Context.getSourceManager();
    if (auto Entry =
            SM.getFileEntryRefForID(SM.getFileID(SM.getExpansionLoc(Location))))
      if (auto Path = getCanonicalPath(*Entry, SM.getFileManager()))
        SeenFiles.insert(*Path);
  }

  const Signature &Original;
  const Signature &Requested;
  const SymbolID &RootID;
  bool Structural = false;
  bool Reorder = false;
  bool TypeChange = false;
  llvm::StringMap<FileChanges> Changes;
  std::set<std::string> SeenFiles;
};

class PreviewFS : public ThreadsafeFS {
public:
  PreviewFS(const ThreadsafeFS &Base, const llvm::StringMap<std::string> &Files)
      : Base(Base), Files(Files) {}

private:
  llvm::IntrusiveRefCntPtr<llvm::vfs::FileSystem> viewImpl() const override {
    auto Overlay = llvm::makeIntrusiveRefCnt<llvm::vfs::OverlayFileSystem>(
        Base.view(std::nullopt));
    auto Memory = llvm::makeIntrusiveRefCnt<llvm::vfs::InMemoryFileSystem>();
    for (const auto &File : Files)
      Memory->addFile(File.getKey(), 0,
                      llvm::MemoryBuffer::getMemBufferCopy(File.getValue()));
    Overlay->pushOverlay(std::move(Memory));
    return Overlay;
  }

  const ThreadsafeFS &Base;
  const llvm::StringMap<std::string> &Files;
};

class BindingUses : public RecursiveASTVisitor<BindingUses> {
public:
  BindingUses(const ParmVarDecl &Parameter, Rewrite &Changes,
              ASTContext &Context, std::optional<llvm::StringRef> NewName)
      : Parameter(Parameter), Changes(Changes), Context(Context),
        NewName(NewName) {}
  bool VisitDeclRefExpr(DeclRefExpr *Reference) {
    if (Reference->getDecl() != &Parameter)
      return true;
    if (!NewName)
      Failure = reject("Cannot remove a parameter used in a function body");
    else
      Failure = Changes.edit(
          Context, CharSourceRange::getTokenRange(Reference->getLocation()),
          *NewName);
    return !Failure;
  }
  llvm::Error Failure = llvm::Error::success();

private:
  const ParmVarDecl &Parameter;
  Rewrite &Changes;
  ASTContext &Context;
  std::optional<llvm::StringRef> NewName;
};

class Visitor : public RecursiveASTVisitor<Visitor> {
public:
  Visitor(Rewrite &Changes, ASTContext &Context)
      : Changes(Changes), Context(Context) {}

  bool VisitFunctionDecl(FunctionDecl *Function) {
    if (!Changes.matches(*Function) || Function->isImplicit())
      return true;
    Failure = declaration(*Function);
    return !Failure;
  }
  bool VisitCallExpr(CallExpr *Call) {
    auto *Function = Call->getDirectCallee();
    if (!Function || !Changes.matches(*Function))
      return true;
    DirectCallees.insert(Call->getCallee()->IgnoreParenImpCasts());
    Changes.note(Context, Call->getExprLoc());
    if (Changes.Structural)
      Failure = call(*Call);
    return !Failure;
  }
  bool VisitDeclRefExpr(DeclRefExpr *Reference) {
    if (auto *Function = llvm::dyn_cast<FunctionDecl>(Reference->getDecl());
        Function && Changes.matches(*Function))
      References.insert(Reference);
    return true;
  }
  bool VisitMemberExpr(MemberExpr *Reference) {
    if (auto *Function =
            llvm::dyn_cast<FunctionDecl>(Reference->getMemberDecl());
        Function && Changes.matches(*Function))
      References.insert(Reference);
    return true;
  }
  llvm::Error finish() {
    if (Failure)
      return std::move(Failure);
    for (const Expr *Reference : References) {
      Changes.note(Context, Reference->getExprLoc());
      if ((Changes.Structural || Changes.TypeChange) &&
          !DirectCallees.contains(Reference))
        return reject("A function value or indirect reference cannot be "
                      "rewritten safely");
    }
    return llvm::Error::success();
  }
  llvm::Error Failure = llvm::Error::success();

private:
  llvm::Error declaration(const FunctionDecl &Function) {
    if (!virtualRoot(&Function))
      return reject("A related method overrides more than one base method");
    if (!supported(Function) ||
        Function.getNumParams() != Changes.Original.Parameters.size())
      return reject("A related declaration has an unsupported signature");
    const auto FunctionLoc = Function.getFunctionTypeLoc();
    if (!FunctionLoc)
      return reject("Function parameter delimiters are unavailable");
    Changes.note(Context, Function.getLocation());
    auto ParameterRange =
        SourceRange(FunctionLoc.getLParenLoc(), FunctionLoc.getRParenLoc());
    auto OldList = Changes.text(Context, ParameterRange);
    if (!OldList)
      return OldList.takeError();
    if (OldList->contains("//") || OldList->contains("/*"))
      return reject("The parameter list contains comments that would be lost");
    if ((Changes.Structural || Changes.TypeChange) &&
        Function.getDeclContext()->isDependentContext())
      return reject("Dependent function declarations are unsupported");
    if (Changes.Structural || Changes.TypeChange) {
      for (const NamedDecl *Other :
           Function.getDeclContext()->lookup(Function.getDeclName())) {
        const auto *Overload = llvm::dyn_cast<FunctionDecl>(Other);
        if (llvm::isa<FunctionTemplateDecl>(Other) ||
            (Overload &&
             Overload->getCanonicalDecl() != Function.getCanonicalDecl() &&
             Changes.Requested.Parameters.size() >=
                 Overload->getMinRequiredArguments() &&
             (Overload->isVariadic() ||
              Changes.Requested.Parameters.size() <= Overload->getNumParams())))
          return reject(
              "The changed signature could alter overload resolution");
      }
    }

    const Stmt *Body =
        Function.doesThisDeclarationHaveABody() ? Function.getBody() : nullptr;
    std::vector<std::string> Parameters;
    bool HasOmittedDefault = false;
    std::set<std::string> Names;
    for (const Parameter &Param : Changes.Requested.Parameters) {
      if (!Param.OldIndex) {
        if (HasOmittedDefault || !Names.insert(Param.Name).second)
          return reject("A new required parameter follows a default or "
                        "conflicts with a name");
        if (Body) {
          auto BodyText = Changes.text(Context, Body->getSourceRange());
          if (!BodyText)
            return BodyText.takeError();
          if (BodyText->contains(Param.Name))
            return reject("A new parameter name may capture an existing name "
                          "in the body");
        }
        Parameters.push_back(Param.Type + " " + Param.Name);
        continue;
      }
      const ParmVarDecl &Existing = *Function.getParamDecl(*Param.OldIndex);
      const Parameter &Original = Changes.Original.Parameters[*Param.OldIndex];
      const std::string ExistingName = Existing.getNameAsString();
      auto Name = Param.Name == Original.Name ? ExistingName : Param.Name;
      if ((!Name.empty() && !Names.insert(Name).second) ||
          (HasOmittedDefault && !Existing.hasDefaultArg()))
        return reject("Conflicting parameter names or a required parameter "
                      "after a default");
      HasOmittedDefault |= Existing.hasDefaultArg();
      if (Existing.hasAttrs() || Existing.isParameterPack() ||
          Existing.getType()->isArrayType() ||
          Existing.getType()->isFunctionPointerType())
        return reject("Attributed, array, pack, or function-pointer parameters "
                      "are unsupported");
      if (Name != ExistingName && Body) {
        auto BodyText = Changes.text(Context, Body->getSourceRange());
        if (!BodyText)
          return BodyText.takeError();
        if (BodyText->contains(Name))
          return reject(
              "Renaming this parameter may capture a name in the body");
        BindingUses Uses(Existing, Changes, Context, Name);
        Uses.TraverseStmt(const_cast<Stmt *>(Body));
        if (Uses.Failure)
          return std::move(Uses.Failure);
      }
      auto Type = Param.Type == Original.Type ? Existing.getType().getAsString()
                                              : Param.Type;
      if (Name == ExistingName && Param.Type == Original.Type) {
        auto Text = Changes.text(Context, Existing.getSourceRange());
        if (!Text)
          return Text.takeError();
        Parameters.push_back(Text->str());
      } else {
        std::string Text = Type + (Name.empty() ? "" : " " + Name);
        if (Existing.hasDefaultArg() && !Existing.hasInheritedDefaultArg()) {
          auto Default = Changes.text(Context, Existing.getDefaultArgRange());
          if (!Default)
            return Default.takeError();
          Text += " = " + Default->str();
        }
        Parameters.push_back(std::move(Text));
      }
    }
    if (Body) {
      for (const auto *Param : Function.parameters()) {
        if (llvm::any_of(
                Changes.Requested.Parameters, [&](const Parameter &Item) {
                  return Item.OldIndex == Param->getFunctionScopeIndex();
                }))
          continue;
        BindingUses Uses(*Param, Changes, Context, std::nullopt);
        Uses.TraverseStmt(const_cast<Stmt *>(Body));
        if (Uses.Failure)
          return std::move(Uses.Failure);
      }
    }
    if (auto Error = Changes.edit(
            Context, CharSourceRange::getTokenRange(ParameterRange),
            "(" + llvm::join(Parameters, ", ") + ")"))
      return Error;
    if (Changes.Requested.ReturnType != Changes.Original.ReturnType) {
      if (Function.getReturnType()->isUndeducedType() ||
          (FunctionLoc.getAs<FunctionProtoTypeLoc>() &&
           FunctionLoc.getAs<FunctionProtoTypeLoc>()
               .getTypePtr()
               ->hasTrailingReturn()))
        return reject("Deduced and trailing C++ return types are unsupported");
      return Changes.edit(
          Context,
          CharSourceRange::getTokenRange(Function.getReturnTypeSourceRange()),
          Changes.Requested.ReturnType);
    }
    return llvm::Error::success();
  }

  llvm::Error call(const CallExpr &Call) {
    if (Call.getExprLoc().isMacroID() || Call.getRParenLoc().isMacroID() ||
        llvm::isa<CXXOperatorCallExpr>(Call))
      return reject("Cannot rewrite a macro or overloaded operator call");
    if (Call.getNumArgs() != Changes.Original.Parameters.size())
      return reject("Call argument count does not match the selected function");
    unsigned Explicit = 0;
    for (auto *Arg : Call.arguments()) {
      const auto *Default = llvm::dyn_cast<CXXDefaultArgExpr>(Arg);
      if (!Default)
        ++Explicit;
    }
    for (unsigned Index = 0; Index < Call.getNumArgs(); ++Index) {
      const Expr *Argument = Call.getArg(Index);
      if (const auto *Default = llvm::dyn_cast<CXXDefaultArgExpr>(Argument))
        Argument = Default->getExpr();
      if ((Changes.Reorder || llvm::none_of(Changes.Requested.Parameters,
                                            [&](const Parameter &Param) {
                                              return Param.OldIndex == Index;
                                            })) &&
          Argument->HasSideEffects(Context))
        return reject(
            "Reordering or removing an argument could change side effects");
    }
    std::vector<std::string> Arguments;
    bool Omitting = false;
    for (const auto &Param : Changes.Requested.Parameters) {
      if (Param.OldIndex && *Param.OldIndex >= Explicit) {
        Omitting = true;
        continue;
      }
      if (Omitting)
        return reject("A defaulted argument would have to become explicit");
      if (!Param.OldIndex) {
        Arguments.push_back(*Param.Argument);
        continue;
      }
      auto Text =
          Changes.text(Context, Call.getArg(*Param.OldIndex)->getSourceRange());
      if (!Text)
        return Text.takeError();
      Arguments.push_back(Text->str());
    }
    if (Explicit == 0) {
      if (Arguments.empty())
        return llvm::Error::success();
      return Changes.edit(Context,
                          CharSourceRange::getCharRange(Call.getRParenLoc(),
                                                        Call.getRParenLoc()),
                          llvm::join(Arguments, ", "));
    }
    const auto Range = SourceRange(Call.getArg(0)->getBeginLoc(),
                                   Call.getArg(Explicit - 1)->getEndLoc());
    auto Previous = Changes.text(Context, Range);
    if (!Previous)
      return Previous.takeError();
    if (Previous->contains("//") || Previous->contains("/*"))
      return reject("Comments inside the argument list would be lost");
    return Changes.edit(Context, CharSourceRange::getTokenRange(Range),
                        llvm::join(Arguments, ", "));
  }

  Rewrite &Changes;
  ASTContext &Context;
  llvm::SmallPtrSet<const Expr *, 16> DirectCallees;
  llvm::SmallPtrSet<const Expr *, 16> References;
};

} // namespace

const FunctionDecl *signatureTarget(ParsedAST &AST, Position Pos) {
  auto Offset = positionToOffset(AST.getSourceManager().getBufferData(
                                     AST.getSourceManager().getMainFileID()),
                                 Pos);
  if (!Offset) {
    llvm::consumeError(Offset.takeError());
    return nullptr;
  }
  const FunctionDecl *Target = nullptr;
  SelectionTree::createEach(
      AST.getASTContext(), AST.getTokens(), *Offset, *Offset,
      [&](SelectionTree Tree) {
        for (auto *Node = Tree.commonAncestor(); Node; Node = Node->Parent) {
          if (const auto *Reference = Node->ASTNode.get<DeclRefExpr>())
            Target = llvm::dyn_cast<FunctionDecl>(Reference->getDecl());
          else if (const auto *Member = Node->ASTNode.get<MemberExpr>())
            Target = llvm::dyn_cast<FunctionDecl>(Member->getMemberDecl());
          else if (Node->ASTNode.get<Stmt>())
            break;
          else
            Target = Node->ASTNode.get<FunctionDecl>();
          if (Target)
            break;
        }
        return Target != nullptr;
      });
  return Target && supported(*Target) ? Target : nullptr;
}

llvm::Expected<llvm::json::Value>
changeSignature(ParsedAST &AST, const ParseInputs &Inputs,
                const GlobalCompilationDatabase &CDB, const ThreadsafeFS &FS,
                const SymbolIndex *Index, Position Pos,
                std::optional<llvm::StringRef> Answer) {
  const FunctionDecl *Target = signatureTarget(AST, Pos);
  if (!Target)
    return reject("Select a supported function or method");
  const auto *Root = virtualRoot(Target);
  if (!Root)
    return reject(
        "A method overriding multiple base methods cannot be changed safely");
  const FunctionDecl *Definition = Root->getDefinition();
  Signature Original = signatureOf(Definition ? *Definition : *Root);
  if (!Answer)
    return toJSON(Original);
  auto Requested = parseSignature(*Answer, Original, AST.getASTContext());
  if (!Requested)
    return Requested.takeError();
  const auto ID = getSymbolID(Root->getCanonicalDecl());
  Rewrite Changes(Original, *Requested, ID);

  std::set<std::string> AffectedFiles;
  if (Index) {
    std::optional<std::string> Unresolved;
    RefsRequest Refs;
    Refs.IDs.insert(ID);
    Refs.IDs.insert(getSymbolID(Target->getCanonicalDecl()));
    auto AddFile = [&](const SymbolLocation &Location) {
      if (Location) {
        auto Path = URI::resolve(Location.FileURI, AST.tuPath());
        if (Path)
          AffectedFiles.insert(std::move(*Path));
        else
          Unresolved = llvm::toString(Path.takeError());
      }
    };
    RelationsRequest Overrides;
    Overrides.Predicate = RelationKind::OverriddenBy;
    Overrides.Subjects.insert(ID);
    while (!Overrides.Subjects.empty()) {
      llvm::DenseSet<SymbolID> Next;
      Index->relations(Overrides,
                       [&](const SymbolID &, const Symbol &Override) {
                         if (Refs.IDs.insert(Override.ID).second)
                           Next.insert(Override.ID);
                         AddFile(Override.CanonicalDeclaration);
                         AddFile(Override.Definition);
                       });
      Overrides.Subjects = std::move(Next);
    }
    LookupRequest Lookup;
    Lookup.IDs = Refs.IDs;
    Index->lookup(Lookup, [&](const Symbol &Symbol) {
      AddFile(Symbol.CanonicalDeclaration);
      AddFile(Symbol.Definition);
    });
    if (Index->refs(Refs,
                    [&](const Ref &Reference) { AddFile(Reference.Location); }))
      return reject("The index truncated the reference search");
    if (Unresolved)
      return reject("Cannot resolve an indexed file: " + *Unresolved);
  }

  auto Parse = [&](PathRef File, const ParseInputs &Input,
                   bool IsPreview) -> llvm::Expected<ParsedAST> {
    if (isCancelled())
      return reject("Change Signature was cancelled");
    StoreDiags Diagnostics;
    auto Invocation = buildCompilerInvocation(Input, Diagnostics);
    if (!Invocation)
      return reject("Cannot load compile settings for " + File);
    auto Parsed = ParsedAST::build(File, Input, std::move(Invocation),
                                   Diagnostics.take(), nullptr);
    if (!Parsed)
      return reject("Cannot parse referred translation unit " + File);
    for (const Diag &Diagnostic : Parsed->getDiagnostics())
      if (Diagnostic.Severity >= DiagnosticsEngine::Error)
        return reject(
            (IsPreview
                 ? "The proposed signature does not compile in "
                 : "Cannot resolve references because of a compile error in ") +
            File + ": " + Diagnostic.Message);
    return std::move(*Parsed);
  };

  std::vector<std::pair<std::string, ParseInputs>> Scanned;
  auto Scan = [&](PathRef File, ParseInputs Input) -> llvm::Error {
    auto Parsed = Parse(File, Input, false);
    if (!Parsed)
      return Parsed.takeError();
    Visitor Visitor(Changes, Parsed->getASTContext());
    Visitor.TraverseDecl(Parsed->getASTContext().getTranslationUnitDecl());
    Scanned.emplace_back(File, std::move(Input));
    return Visitor.finish();
  };
  if (auto Error = Scan(AST.tuPath(), Inputs))
    return std::move(Error);
  for (const std::string &Path : AffectedFiles) {
    if (Changes.SeenFiles.count(Path) != 0)
      continue;
    auto Command = CDB.getCompileCommand(Path);
    if (!Command)
      return reject(
          "Missing compilation database entry for indexed reference in " +
          Path);
    auto Buffer = FS.view(std::nullopt)->getBufferForFile(Path);
    if (!Buffer)
      return reject("Cannot read indexed reference in " + Path);
    ParseInputs Input{std::move(*Command), &FS, (*Buffer)->getBuffer().str()};
    if (auto Error = Scan(Path, std::move(Input)))
      return std::move(Error);
    if (Changes.SeenFiles.count(Path) == 0)
      return reject("An indexed occurrence could not be re-resolved in " +
                    Path);
  }

  llvm::StringMap<std::string> Rewritten;
  for (const auto &File : Changes.Changes) {
    if (File.getValue().Edits.empty())
      continue;
    auto Text = tooling::applyAllReplacements(File.getValue().Original,
                                              File.getValue().Edits);
    if (!Text)
      return Text.takeError();
    Rewritten.try_emplace(File.getKey(), std::move(*Text));
  }
  if (!Rewritten.empty()) {
    PreviewFS Overlay(FS, Rewritten);
    for (auto &[File, Input] : Scanned) {
      Input.TFS = &Overlay;
      if (auto Found = Rewritten.find(File); Found != Rewritten.end())
        Input.Contents = Found->getValue();
      if (auto Validated = Parse(File, Input, true); !Validated)
        return Validated.takeError();
    }
  }

  llvm::json::Object Edits;
  llvm::json::Object Originals;
  for (auto &File : Changes.Changes) {
    if (File.getValue().Edits.empty())
      continue;
    auto URI = URIForFile::canonicalize(File.getKey(), AST.tuPath()).uri();
    Edits[URI] = llvm::json::Array(
        replacementsToEdits(File.getValue().Original, File.getValue().Edits));
    Originals[URI] = std::move(File.getValue().Original);
  }
  return llvm::json::Object{
      {"edit", llvm::json::Object{{"changes", std::move(Edits)}}},
      {"originals", std::move(Originals)},
      {"warnings",
       llvm::json::Array{
           "Only visible declarations and indexed references are included. "
           "External or inactive callers may need changes.",
           "Review type and return changes and rebuild affected translation "
           "units after applying."}}};
}

} // namespace clang::clangd
