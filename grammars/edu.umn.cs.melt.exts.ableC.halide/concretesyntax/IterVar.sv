grammar edu:umn:cs:melt:exts:ableC:halide:concretesyntax;

marking terminal MultiFor_t 'forall' lexer classes {Ckeyword};

concrete productions top::Stmt_c
| 'forall' '(' ivs::IterVars_c ')' body::Stmt_c
  { top.ast = multiForStmt(ivs.ast, body.ast); }
  
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