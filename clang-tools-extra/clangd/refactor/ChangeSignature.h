//===--- ChangeSignature.h - Semantic signature edits -----------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_CLANG_TOOLS_EXTRA_CLANGD_REFACTOR_CHANGESIGNATURE_H
#define LLVM_CLANG_TOOLS_EXTRA_CLANGD_REFACTOR_CHANGESIGNATURE_H

#include "Protocol.h"
#include "support/Path.h"
#include "llvm/Support/JSON.h"
#include <optional>

namespace clang {
class FunctionDecl;
namespace clangd {
class GlobalCompilationDatabase;
class ParsedAST;
class SymbolIndex;
class ThreadsafeFS;
struct ParseInputs;

const FunctionDecl *signatureTarget(ParsedAST &AST, Position Pos);

llvm::Expected<llvm::json::Value>
changeSignature(ParsedAST &AST, const ParseInputs &Inputs,
                const GlobalCompilationDatabase &CDB, const ThreadsafeFS &FS,
                const SymbolIndex *Index, Position Pos,
                std::optional<llvm::StringRef> Answer, bool Force);

} // namespace clangd
} // namespace clang

#endif
