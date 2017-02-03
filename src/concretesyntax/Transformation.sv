grammar edu:umn:cs:melt:exts:ableC:halide:src:concretesyntax;

terminal Split_t 'split' lexer classes {Ckeyword};
terminal Into_t 'into' lexer classes {Ckeyword};

closed nonterminal Transformations_c with ast<Transformation>;

concrete productions top::Transformation_c
| h::Transformation_c t::Transformations_c
  { top.ast = seqTransformation(h.ast, t.ast); }
| 
  { top.ast = nullTransformation(); }

closed nonterminal Transformation_c with ast<Transformation>;

concrete productions top::Transformation_c
| 'split' id::Identifier_t 'into' '(' iv::IterVar_c ivs::IterVars_c ')' ';'
  { top.ast = splitTransformation(fromId(id), iv.ast, ivs.ast); }