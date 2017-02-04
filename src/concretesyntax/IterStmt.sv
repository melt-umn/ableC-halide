grammar edu:umn:cs:melt:exts:ableC:halide:src:concretesyntax;

-- For double-brace-enclosed statments
-- We need to use the RCurly_t terminal from ableC to close the scope, to avoid issues with the mda
-- The lexer hack parser action for this closes two scopes, so we need to open two scopes to balance this
terminal DoubleLBrace_t '{{'
  action { context = head(context) :: head(context) :: context; },
  lexer classes {Ckeyword};

nonterminal IterStmts_c with ast<IterStmt>;

concrete productions top::IterStmts_c
| h::IterStmt_c t::IterStmts_c
  { top.ast = seqIterStmt(h.ast, t.ast); }
| 
  { top.ast = nullIterStmt(); }

nonterminal IterStmt_c with ast<IterStmt>;

concrete productions top::IterStmt_c
| '{' is::IterStmts_c '}'
  { top.ast = is.ast; }
| '{{' l::BlockItemList_c '}' '}'
  { top.ast = stmtIterStmt(foldStmt(l.ast)); }
| e::Expr_c ';'
  { top.ast = stmtIterStmt(exprStmt(e.ast)); }
| 'for' '(' ivs::IterVars_c ')' body::IterStmt_c
  { top.ast = multiForIterStmt(ivs.ast, body.ast); }
  
nonterminal IterVars_c with ast<IterVars>;

concrete productions top::IterVars_c
(consIterVar_c) | ds::DeclarationSpecifiers_c d::Declarator_c ':' cutoff::AssignExpr_c ',' rest::IterVars_c
  { ds.givenQualifiers = ds.typeQualifiers;
    d.givenType = baseTypeExpr();
    local bt :: BaseTypeExpr =
      figureOutTypeFromSpecifiers(ds.location, ds.typeQualifiers, ds.preTypeSpecifiers, ds.realTypeSpecifiers, ds.mutateTypeSpecifiers);
    top.ast = consIterVar(bt, d.ast, d.declaredIdent, cutoff.ast, rest.ast); }
(consAnonIterVar_c) | cutoff::AssignExpr_c ',' rest::IterVars_c
  { top.ast = consAnonIterVar(cutoff.ast, rest.ast); }
| ds::DeclarationSpecifiers_c d::Declarator_c ':' cutoff::AssignExpr_c
  { forwards to consIterVar_c(ds, d, $3, cutoff, ',', nilIterVar_c()); }
| cutoff::AssignExpr_c
  { forwards to consAnonIterVar_c(cutoff, ',', nilIterVar_c()); }
(nilIterVar_c) | 
  { top.ast = nilIterVar(); }
  
nonterminal IterVar_c with ast<IterVar>;

concrete productions top::IterVar_c
| ds::DeclarationSpecifiers_c d::Declarator_c
  { ds.givenQualifiers = ds.typeQualifiers;
    d.givenType = baseTypeExpr();
    local bt :: BaseTypeExpr =
      figureOutTypeFromSpecifiers(ds.location, ds.typeQualifiers, ds.preTypeSpecifiers, ds.realTypeSpecifiers, ds.mutateTypeSpecifiers);
    top.ast = iterVar(bt, d.ast, d.declaredIdent); }