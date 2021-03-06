grammar edu:umn:cs:melt:exts:ableC:halide:concretesyntax;

imports edu:umn:cs:melt:ableC:concretesyntax;
imports silver:langutil only ast;

imports edu:umn:cs:melt:ableC:abstractsyntax:host;
imports edu:umn:cs:melt:ableC:abstractsyntax:construction;
imports edu:umn:cs:melt:ableC:abstractsyntax:env;

imports edu:umn:cs:melt:exts:ableC:halide:abstractsyntax;

marking terminal Transform_t 'transform' lexer classes {Keyword, Global};

terminal By_t 'by' lexer classes {Keyword};

concrete productions top::IterationStmt_c
| 'transform' '{' s::BlockItemList_c '}' 'by' '{' ts::Transformations_c '}'
  { top.ast = transformStmt(foldStmt(s.ast), ts.ast); }
