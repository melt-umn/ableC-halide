grammar edu:umn:cs:melt:exts:ableC:halide:src:concretesyntax;

imports edu:umn:cs:melt:ableC:concretesyntax;
imports silver:langutil only ast;

imports edu:umn:cs:melt:ableC:abstractsyntax;
imports edu:umn:cs:melt:ableC:abstractsyntax:construction;
imports edu:umn:cs:melt:ableC:abstractsyntax:env;

imports edu:umn:cs:melt:exts:ableC:halide:src:abstractsyntax;

marking terminal Transform_t 'transform' lexer classes {Ckeyword};

terminal By_t 'by' lexer classes {Ckeyword};

concrete productions top::IterationStmt_c
| 'transform' '{' is::IterStmts_c '}' 'by' '{' ts::Transformations_c '}'
  { top.ast = iterateStmt(is.ast, ts.ast); }