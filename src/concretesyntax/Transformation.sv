grammar edu:umn:cs:melt:exts:ableC:halide:src:concretesyntax;

terminal Split_t       'split'       lexer classes {Ckeyword};
terminal Reorder_t     'reorder'     lexer classes {Ckeyword};
terminal Tile_t        'tile'        lexer classes {Ckeyword};
terminal Unroll_t      'unroll'      lexer classes {Ckeyword};
terminal Parallelize_t 'parallelize' lexer classes {Ckeyword};
terminal Vectorize_t   'vectorize'   lexer classes {Ckeyword};

terminal Into_t        'into'        lexer classes {Ckeyword};
terminal Threads_t     'threads'     lexer classes {Ckeyword};

closed nonterminal Transformations_c with location, ast<Transformation>;

concrete productions top::Transformations_c
| h::Transformation_c t::Transformations_c
  { top.ast = seqTransformation(h.ast, t.ast, location=top.location); }
| 
  { top.ast = nullTransformation(location=top.location); }

closed nonterminal Transformation_c with location, ast<Transformation>;

concrete productions top::Transformation_c
| 'split' id::Identifier_t 'into' '(' iv::IterVar_c ',' ivs::IterVars_c ')' ';'
  { top.ast = splitTransformation(fromId(id), iv.ast, ivs.ast, location=top.location); }
| 'reorder' names::Names_c ';'
  { top.ast = reorderTransformation(names.ast, location=top.location); }
| 'tile' names::Names_c 'into' '(' ics::IntConstants_c ')' ';'
  { top.ast = tileTransformation(names.ast, ics.ast, location=top.location); }
| 'unroll' id::Identifier_t ';'
  { top.ast = unrollTransformation(fromId(id), location=top.location); }
| 'parallelize' id::Identifier_t ';'
  { top.ast = parallelizeTransformation(fromId(id), nothing(), location=top.location); }
| 'parallelize' id::Identifier_t 'into' '(' n::DecConstant_t ')' 'threads' ';'
  { top.ast = parallelizeTransformation(fromId(id), just(toInt(n.lexeme)), location=top.location); }
| 'vectorize' id::Identifier_t ';'
  { top.ast = vectorizeTransformation(fromId(id), location=top.location); }

closed nonterminal Names_c with ast<Names>;

concrete productions top::Names_c
| h::Identifier_t ',' t::Names_c
  { top.ast = consName(fromId(h), t.ast); }
| h::Identifier_t
  { top.ast = consName(fromId(h), nilName()); }
| 
  { top.ast = nilName(); }

closed nonterminal IntConstants_c with ast<[Integer]>;

concrete productions top::IntConstants_c
| h::DecConstant_t ',' t::IntConstants_c
  { top.ast = toInt(h.lexeme) :: t.ast; }
| h::DecConstant_t
  { top.ast = [toInt(h.lexeme)]; }
| 
  { top.ast = []; }