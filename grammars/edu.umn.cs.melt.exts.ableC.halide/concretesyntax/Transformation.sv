grammar edu:umn:cs:melt:exts:ableC:halide:concretesyntax;

terminal Split_t       'split'       lexer classes {Keyword};
terminal Reorder_t     'reorder'     lexer classes {Keyword};
terminal Tile_t        'tile'        lexer classes {Keyword};
terminal Unroll_t      'unroll'      lexer classes {Keyword};
terminal Parallelize_t 'parallelize' lexer classes {Keyword};
terminal Vectorize_t   'vectorize'   lexer classes {Keyword};

terminal Into_t        'into'        lexer classes {Keyword, Global};
terminal Threads_t     'threads'     lexer classes {Keyword};

closed tracked nonterminal Transformations_c with ast<Transformation>;

concrete productions top::Transformations_c
| h::Transformation_c t::Transformations_c
  { top.ast = seqTransformation(h.ast, t.ast); }
| 
  { top.ast = nullTransformation(); }

closed tracked nonterminal Transformation_c with ast<Transformation>;

concrete productions top::Transformation_c
| 'split' id::Identifier_t 'into' '(' iv::IterVar_c ',' ivs::IterVars_c ')' ';'
  { top.ast = splitTransformation(fromId(id), iv.ast, ivs.ast); }
| 'reorder' names::Names_c ';'
  { top.ast = reorderTransformation(names.ast); }
| 'tile' names::Names_c 'into' '(' ics::IntConstants_c ')' ';'
  { top.ast = tileTransformation(names.ast, ics.ast); }
| 'unroll' id::Identifier_t ';'
  { top.ast = unrollTransformation(fromId(id)); }
| 'parallelize' id::Identifier_t ';'
  { top.ast = parallelizeTransformation(fromId(id), nothing()); }
| 'parallelize' id::Identifier_t 'into' '(' n::DecConstant_t ')' 'threads' ';'
  { top.ast = parallelizeTransformation(fromId(id), just(toInteger(n.lexeme))); }
| 'vectorize' id::Identifier_t ';'
  { top.ast = vectorizeTransformation(fromId(id)); }

closed tracked nonterminal Names_c with ast<Names>;

concrete productions top::Names_c
| h::Identifier_t ',' t::Names_c
  { top.ast = consName(fromId(h), t.ast); }
| h::Identifier_t
  { top.ast = consName(fromId(h), nilName()); }
| 
  { top.ast = nilName(); }

closed tracked nonterminal IntConstants_c with ast<[Integer]>;

concrete productions top::IntConstants_c
| h::DecConstant_t ',' t::IntConstants_c
  { top.ast = toInteger(h.lexeme) :: t.ast; }
| h::DecConstant_t
  { top.ast = [toInteger(h.lexeme)]; }
| 
  { top.ast = []; }
