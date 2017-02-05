grammar edu:umn:cs:melt:exts:ableC:halide:src:concretesyntax;

terminal Split_t   'split'   lexer classes {Ckeyword};
terminal Into_t    'into'    lexer classes {Ckeyword};
terminal Reorder_t 'reorder' lexer classes {Ckeyword};

closed nonterminal Transformations_c with ast<Transformation>;

concrete productions top::Transformations_c
| h::Transformation_c t::Transformations_c
  { top.ast = seqTransformation(h.ast, t.ast); }
| 
  { top.ast = nullTransformation(); }

closed nonterminal Transformation_c with ast<Transformation>;

concrete productions top::Transformation_c
| 'split' id::Identifier_t 'into' '(' iv::IterVar_c ',' ivs::IterVars_c ')' ';'
  { top.ast = splitTransformation(fromId(id), iv.ast, ivs.ast); }
| 'reorder' names::Names_c ';'
  { top.ast = reorderTransformation(names.ast); }

closed nonterminal Names_c with ast<Names>;

concrete productions top::Names_c
| h::Identifier_t ',' t::Names_c
  { top.ast = consName(fromId(h), t.ast); }
| h::Identifier_t
  { top.ast = consName(fromId(h), nilName()); }
| 
  { top.ast = nilName(); }