grammar edu:umn:cs:melt:exts:ableC:halide:abstractsyntax;

inherited attribute iterStmtIn::IterStmt;
synthesized attribute iterStmtOut::IterStmt;

nonterminal Transformation with location, pp, errors, iterStmtIn, iterStmtOut, env, returnType;

abstract production nullTransformation
top::Transformation ::= 
{
  top.pp = notext();
  top.errors := [];
  top.iterStmtOut = top.iterStmtIn;
}

abstract production seqTransformation
top::Transformation ::= h::Transformation t::Transformation
{
  top.pp = ppConcat([h.pp, line(), t.pp]);
  top.errors := if !null(h.errors) then h.errors else t.errors;
  
  h.iterStmtIn = top.iterStmtIn;
  t.iterStmtIn = h.iterStmtOut;
  top.iterStmtOut = t.iterStmtOut;
}

abstract production splitTransformation
top::Transformation ::= n::Name iv::IterVar ivs::IterVars
{
  top.pp = pp"split ${n.pp} into (${iv.pp}, ${ivs.pp});";
  top.errors := iv.errors ++ ivs.errors;
  
  top.errors <-
     if !null(iterStmt.errors)
     then iterStmt.errors
     else (if !null(n.valueLookupCheck)
           then [err(n.location, n.name ++ " is not a transformable loop")]
           else []);
  
  n.env = addEnv(iterStmt.iterDefs, emptyEnv()); -- Env for name lookup consists of only the transformable loop variables
 
  local iterStmt::IterStmt = top.iterStmtIn;
  iterStmt.target = n;
  iterStmt.newIterVar = iv;
  iterStmt.newIterVars = ivs;
  iterStmt.env = top.env;
  iterStmt.returnType = top.returnType;
  
  top.iterStmtOut = iterStmt.splitTrans;
}

abstract production anonSplitTransformation
top::Transformation ::= n::Name ivs::IterVars
{
  top.pp = pp"split ${n.pp} into (_, ${ivs.pp});";

  local iterStmt::IterStmt = top.iterStmtIn;
  iterStmt.env = top.env;
  iterStmt.returnType = top.returnType;
  
  n.env = addEnv(iterStmt.iterDefs, emptyEnv());
  
  forwards to
    splitTransformation(
      n,
      iterVar(
        directTypeExpr(n.valueItem.typerep),
        baseTypeExpr(),
        name("_iter_var_" ++ toString(genInt()), location=builtin)),
      ivs,
      location=top.location);
}

abstract production reorderTransformation
top::Transformation ::= ns::Names
{
  top.pp = pp"reorder ${ppImplode(pp", ", ns.pps)};";
  top.errors :=
     if !null(iterStmt.errors)
     then iterStmt.errors
     else if !null(ns.loopLookupChecks)
     then ns.loopLookupChecks
     else iterStmt.reorderErrors;
  
  ns.env = addEnv(iterStmt.iterDefs, emptyEnv());
 
  local iterStmt::IterStmt = top.iterStmtIn;
  iterStmt.targets = ns;
  iterStmt.env = top.env;
  iterStmt.returnType = top.returnType;
  
  top.iterStmtOut = iterStmt.reorderTrans;
}

abstract production tileTransformation
top::Transformation ::= ns::Names sizes::[Integer]
{
  top.pp =
    cat(
      pp"tile ${ppImplode(pp", ", ns.pps)} ",
      pp"into (${text(implode(", ", map(\ i::Integer -> toString(i), sizes)))});");
  top.errors :=
     (if ns.count != length(sizes)
      then [err(top.location, s"Incorrect tile dimension: Expected ${toString(ns.count)}, got ${toString(length(sizes))}")]
      else []) ++
     if !null(iterStmt.errors)
     then iterStmt.errors
     else if !null(ns.loopLookupChecks)
     then ns.loopLookupChecks
     else if !null(iterStmt.reorderErrors)
     then iterStmt.reorderErrors
     else forward.errors;
  
  ns.tileSize = sizes;
  ns.tileInnerNamesIn = ns.tileInnerNames;
  ns.env = addEnv(iterStmt.iterDefs, emptyEnv());
  
  -- Decorate iterStmtIn to check loops are contiguous before splitting loops and reordering via forward
  local iterStmt::IterStmt = top.iterStmtIn;
  iterStmt.targets = ns;
  iterStmt.env = top.env;
  iterStmt.returnType = top.returnType;
  
  forwards to
    seqTransformation(
      ns.tileTransformation,
      reorderTransformation(ns.tileNames, location=builtin),
      location=builtin);
}

abstract production unrollTransformation
top::Transformation ::= n::Name
{
  top.pp = pp"unroll ${n.pp};";
  top.errors :=
     if !null(iterStmt.errors)
     then iterStmt.errors
     else (if !null(n.valueLookupCheck)
           then [err(n.location, n.name ++ " is not a transformable loop")]
           else []) ++ iterStmt.unrollErrors;
  
  n.env = addEnv(iterStmt.iterDefs, emptyEnv());
  
  local iterStmt::IterStmt = top.iterStmtIn;
  iterStmt.target = n;
  iterStmt.env = top.env;
  iterStmt.returnType = top.returnType;
  
  top.iterStmtOut = iterStmt.unrollTrans;
}

abstract production parallelizeTransformation
top::Transformation ::= n::Name numThreads::Maybe<Integer>
{
  local numThreadsPP::Document =
    case numThreads of
      just(n) -> pp" into (${text(toString(n))}) threads"
    | nothing() -> notext()
    end;
  top.pp = pp"parallelize ${n.pp}${numThreadsPP};";
  top.errors :=
     if !null(iterStmt.errors)
     then iterStmt.errors
     else (if !null(n.valueLookupCheck)
           then [err(n.location, n.name ++ " is not a transformable loop")]
           else []) ++ iterStmt.parallelizeErrors;
  
  n.env = addEnv(iterStmt.iterDefs, emptyEnv());
  
  local iterStmt::IterStmt = top.iterStmtIn;
  iterStmt.target = n;
  iterStmt.inParallel = false;
  iterStmt.inVector = false;
  iterStmt.numThreads = numThreads;
  iterStmt.env = top.env;
  iterStmt.returnType = top.returnType;
  
  top.iterStmtOut = iterStmt.parallelizeTrans;
}

abstract production vectorizeTransformation
top::Transformation ::= n::Name
{
  top.pp = pp"vectorize ${n.pp};";
  top.errors :=
     if !null(iterStmt.errors)
     then iterStmt.errors
     else (if !null(n.valueLookupCheck)
           then [err(n.location, n.name ++ " is not a transformable loop")]
           else []) ++ iterStmt.vectorizeErrors;
  
  n.env = addEnv(iterStmt.iterDefs, emptyEnv());
  
  local iterStmt::IterStmt = top.iterStmtIn;
  iterStmt.target = n;
  iterStmt.inParallel = false;
  iterStmt.inVector = false;
  iterStmt.env = top.env;
  iterStmt.returnType = top.returnType;
  
  top.iterStmtOut = iterStmt.vectorizeTrans;
}

synthesized attribute loopLookupChecks::[Message] occurs on Names;

aspect production consName
top::Names ::= h::Name t::Names
{
  top.loopLookupChecks =
    (if !null(h.valueLookupCheck)
     then [err(h.location, h.name ++ " is not a transformable loop")]
     else []) ++ t.loopLookupChecks;
}

aspect production nilName
top::Names ::= 
{
  top.loopLookupChecks = [];
}

-- Parameter attributes for various transformations
autocopy attribute target::Name occurs on IterStmt;
autocopy attribute targets::Names occurs on IterStmt;
autocopy attribute newIterVar::IterVar occurs on IterStmt;
autocopy attribute newIterVars::IterVars occurs on IterStmt;

autocopy attribute insertedTransFn::(IterStmt ::= IterStmt) occurs on IterStmt;
autocopy attribute inParallel::Boolean occurs on IterStmt;
autocopy attribute numThreads::Maybe<Integer> occurs on IterStmt;
autocopy attribute inVector::Boolean occurs on IterStmt;

-- Functor attributes that perform various transformations
functor attribute splitTrans occurs on IterStmt;
functor attribute insertTrans occurs on IterStmt;
functor attribute reorderTrans occurs on IterStmt;
functor attribute unrollTrans occurs on IterStmt;
functor attribute parallelizeTrans occurs on IterStmt;
functor attribute vectorizeTrans occurs on IterStmt;

-- Monoid attributes to collect errors for various transformations
synthesized attribute reorderErrors::[Message] occurs on IterStmt;
synthesized attribute unrollErrors::[Message] occurs on IterStmt;
synthesized attribute parallelizeErrors::[Message] occurs on IterStmt;
synthesized attribute vectorizeErrors::[Message] occurs on IterStmt;

-- Other misc analysis attributes used by various transformations
synthesized attribute isParallel::Boolean occurs on IterStmt;
synthesized attribute isVector::Boolean occurs on IterStmt;

-- Aspects for base cases for various transformations
aspect default production
top::IterStmt ::= 
{
  top.insertTrans = top.insertedTransFn(top);
  top.reorderConstructors = [];
  top.reorderBaseIterStmt = top;
}

aspect production nullIterStmt
top::IterStmt ::= 
{
  propagate splitTrans, reorderTrans, unrollTrans, parallelizeTrans, vectorizeTrans;
  
  top.reorderErrors = [];
  top.unrollErrors = [];
  top.parallelizeErrors = [];
  top.vectorizeErrors = [];
  
  top.isParallel = false;
  top.isVector = false;
}

aspect production seqIterStmt
top::IterStmt ::= h::IterStmt t::IterStmt
{
  propagate splitTrans, reorderTrans, unrollTrans, parallelizeTrans, vectorizeTrans;
  
  top.reorderErrors = h.reorderErrors ++ t.reorderErrors;
  top.unrollErrors = h.unrollErrors ++ t.unrollErrors;
  top.parallelizeErrors = h.parallelizeErrors ++ t.parallelizeErrors;
  top.vectorizeErrors = h.vectorizeErrors ++ t.vectorizeErrors;
  
  top.isParallel = h.isParallel || t.isParallel;
  top.isVector = h.isVector || t.isVector;
}

aspect production compoundIterStmt
top::IterStmt ::= is::IterStmt
{
  propagate splitTrans, reorderTrans, unrollTrans, parallelizeTrans, vectorizeTrans;
  
  top.reorderErrors = is.reorderErrors;
  top.unrollErrors = is.unrollErrors;
  top.parallelizeErrors = is.parallelizeErrors;
  top.vectorizeErrors = is.vectorizeErrors;
  
  top.isParallel = is.isParallel;
  top.isVector = is.isVector;
}

aspect production stmtIterStmt
top::IterStmt ::= s::Stmt
{
  propagate splitTrans, reorderTrans, unrollTrans, parallelizeTrans, vectorizeTrans;
  
  top.reorderErrors = [];
  top.unrollErrors = [];
  top.parallelizeErrors = [];
  top.vectorizeErrors = [];
  
  top.isParallel = false;
  top.isVector = false;
}

aspect production condIterStmt
top::IterStmt ::= cond::Expr th::IterStmt el::IterStmt
{
  propagate splitTrans, reorderTrans, unrollTrans, parallelizeTrans, vectorizeTrans;
  
  top.reorderErrors = th.reorderErrors ++ el.reorderErrors;
  top.unrollErrors = th.unrollErrors ++ el.unrollErrors;
  top.parallelizeErrors = th.parallelizeErrors ++ el.parallelizeErrors;
  top.vectorizeErrors = th.vectorizeErrors ++ el.vectorizeErrors;
  
  top.isParallel = th.isParallel || el.isParallel;
  top.isVector = th.isVector || el.isVector;
}

aspect production parallelForIterStmt
top::IterStmt ::= numThreads::Maybe<Integer> bty::BaseTypeExpr mty::TypeModifierExpr n::Name cutoff::Expr body::IterStmt
{
  propagate splitTrans, reorderTrans, unrollTrans, parallelizeTrans, vectorizeTrans;
  
  top.reorderErrors = body.reorderErrors;
  top.unrollErrors = body.unrollErrors;
  top.parallelizeErrors = body.parallelizeErrors;
  top.vectorizeErrors = body.vectorizeErrors;
  
  top.isParallel = true;
  top.isVector = false;
  
  body.inParallel = true;
}

aspect production vectorForIterStmt
top::IterStmt ::= bty::BaseTypeExpr mty::TypeModifierExpr n::Name cutoff::Expr body::IterStmt
{
  propagate splitTrans, reorderTrans, unrollTrans, parallelizeTrans, vectorizeTrans;
  
  top.reorderErrors = body.reorderErrors;
  top.unrollErrors = body.unrollErrors;
  top.parallelizeErrors = body.parallelizeErrors;
  top.vectorizeErrors = body.vectorizeErrors;
  
  top.isParallel = false;
  top.isVector = true;
  
  body.inParallel = true;
  body.inVector = true;
}

-- insertTrans
aspect production forIterStmt
top::IterStmt ::= bty::BaseTypeExpr mty::TypeModifierExpr n::Name cutoff::Expr body::IterStmt
{
  propagate insertTrans;
}

-- splitTrans
synthesized attribute splitIndexTrans::Expr occurs on IterVars;
inherited attribute splitIndexTransIn::Expr occurs on IterVars;

synthesized attribute outerCutoffTrans::Expr occurs on IterVars;

synthesized attribute outerCutoffIsConst::Boolean occurs on IterVars;
synthesized attribute outerCutoffConstVal::Integer occurs on IterVars;

aspect production consIterVar
top::IterVars ::= bty::BaseTypeExpr mty::TypeModifierExpr n::Name cutoff::Expr rest::IterVars
{
  top.splitIndexTrans = rest.splitIndexTrans;
  rest.splitIndexTransIn =
    mkAdd(
      mulExpr(
        top.splitIndexTransIn,
        cutoff,
        location=builtin),
      declRefExpr(n, location=builtin),
      builtin);
  
  top.outerCutoffTrans = 
    mulExpr(
      cutoff,
      rest.outerCutoffTrans,
      location=builtin);
  
  top.outerCutoffIsConst = 
    case cutoff.integerConstantValue of
    | just(n) -> rest.outerCutoffIsConst
    | nothing() -> false
    end;
  
  top.outerCutoffConstVal =
    case cutoff.integerConstantValue of
    | just(n) -> n * rest.outerCutoffConstVal
    | nothing() -> error("cutoff is not a constant")
    end;
}

aspect production nilIterVar
top::IterVars ::= 
{
  top.splitIndexTrans = top.splitIndexTransIn;
  top.outerCutoffTrans = mkIntConst(1, builtin);
  top.outerCutoffIsConst = true;
  top.outerCutoffConstVal = 1;
}

aspect production forIterStmt
top::IterStmt ::= bty::BaseTypeExpr mty::TypeModifierExpr n::Name cutoff::Expr body::IterStmt
{
  local splitTransBody::IterStmt = body;
  splitTransBody.insertedTransFn =
    \ innerBody::IterStmt ->
      compoundIterStmt(
        seqIterStmt(
          stmtIterStmt(
            ableC_Stmt {
              $directTypeExpr{d.typerep} $Name{n} = $Expr{splitIterVars.splitIndexTrans};
            }),
          condIterStmt(
            ltExpr(
              declRefExpr(n, location=builtin),
              cutoff,
              location=builtin),
            innerBody,
            nullIterStmt())));
  splitTransBody.env = top.env;
  splitTransBody.returnType = top.returnType;
  
  local splitIterVars::IterVars = top.newIterVars;
  splitIterVars.splitIndexTransIn = declRefExpr(splitIterVar.iterVarName, location=builtin);
  splitIterVars.forIterStmtBody = splitTransBody.insertTrans;
  splitIterVars.env = top.env;
  splitIterVars.returnType = top.returnType;
  
  local splitIterVar::IterVar = top.newIterVar;
  
  local forIterStmtCutoff::Expr =
    ableC_Expr {
      // Calculate ceil(cutoff/product of split indices)
      1 + ($Expr{cutoff} - 1) / $Expr{splitIterVars.outerCutoffTrans}
    };
  splitIterVar.forIterStmtCutoff =
    case cutoff.integerConstantValue of
    | just(n) -> 
        if splitIterVars.outerCutoffIsConst
        then mkIntConst(1 + (n - 1) / splitIterVars.outerCutoffConstVal, builtin)
        else forIterStmtCutoff
    | nothing() -> forIterStmtCutoff
    end;
  splitIterVar.forIterStmtBody = splitIterVars.forIterStmtTrans;

  top.splitTrans = 
    if n.name == top.target.name
    then splitIterVar.forIterStmtTrans
    else forIterStmt(bty, mty, n, cutoff, body.splitTrans);
}

-- reorderTrans
autocopy attribute reorderConstructorsIn::[Pair<String (IterStmt ::= IterStmt)>] occurs on Names;
autocopy attribute reorderBaseIterStmtIn::IterStmt occurs on Names;

synthesized attribute reorderConstructors::[Pair<String (IterStmt ::= IterStmt)>] occurs on IterStmt;
synthesized attribute reorderBaseIterStmt::IterStmt occurs on IterStmt;

attribute reorderErrors occurs on Names;
attribute reorderTrans<IterStmt> occurs on Names;

aspect production consName
top::Names ::= h::Name t::Names
{
  local reorderLookupRes::Maybe<(IterStmt ::= IterStmt)> =
    lookupBy(stringEq, h.name, top.reorderConstructorsIn);

  top.reorderErrors =
    case reorderLookupRes of
      just(_) ->
        if containsBy(stringEq, h.name, t.names)
        then [err(h.location, s"Duplicate loop name ${h.name}")]
        else []
    | nothing() -> [err(h.location, s"Loop ${h.name} is not contiguous")]
    end ++ t.reorderErrors;
  
  top.reorderTrans = 
    case reorderLookupRes of
      just(fn) -> fn(t.reorderTrans)
    | nothing() -> t.reorderTrans
    end;
}

aspect production nilName
top::Names ::= 
{
  top.reorderErrors = [];
  top.reorderTrans = top.reorderBaseIterStmtIn;
}

aspect production forIterStmt
top::IterStmt ::= bty::BaseTypeExpr mty::TypeModifierExpr n::Name cutoff::Expr body::IterStmt
{
  top.reorderConstructors =
    if containsBy(stringEq, n.name, top.targets.names)
    then pair(n.name, forIterStmt(bty, mty, n, cutoff, _)) :: body.reorderConstructors
    else [];
  
  top.reorderBaseIterStmt =
    if containsBy(stringEq, n.name, top.targets.names)
    then body.reorderBaseIterStmt
    else top;
  
  local reorderTargets::Names = top.targets;
  reorderTargets.reorderConstructorsIn = top.reorderConstructors;
  reorderTargets.reorderBaseIterStmtIn = top.reorderBaseIterStmt;
  
  top.reorderErrors = 
    if containsBy(stringEq, n.name, top.targets.names)
    then reorderTargets.reorderErrors
    else body.reorderErrors;

  top.reorderTrans = 
    if containsBy(stringEq, n.name, top.targets.names)
    then reorderTargets.reorderTrans
    else forIterStmt(bty, mty, n, cutoff, body.reorderTrans);
}

-- tileTrans
autocopy attribute tileSize::[Integer] occurs on Names;
autocopy attribute tileInnerNamesIn::Names occurs on Names;

synthesized attribute tileInnerNames::Names occurs on Names;
synthesized attribute tileNames::Names occurs on Names;
synthesized attribute tileTransformation::Transformation occurs on Names;

aspect production consName
top::Names ::= h::Name t::Names
{
  local innerName::Name = name(h.name ++ "_inner", location=builtin);
  local outerName::Name = name(h.name ++ "_outer", location=builtin);
  
  top.tileInnerNames = consName(innerName, t.tileInnerNames);
  top.tileNames = consName(outerName, t.tileNames);

  top.tileTransformation =
    seqTransformation(
      splitTransformation(
        h,
        iterVar(directTypeExpr(h.valueItem.typerep), baseTypeExpr(), outerName),
        consIterVar(
          directTypeExpr(h.valueItem.typerep),
          baseTypeExpr(),
          innerName,
          mkIntConst(
            if !null(top.tileSize)
            then head(top.tileSize)
            else error("Tile has wrong dimension"),
            builtin),
          nilIterVar()),
        location=builtin),
      t.tileTransformation,
      location=builtin);
  
  t.tileSize = tail(top.tileSize);
}

aspect production nilName
top::Names ::= 
{
  top.tileInnerNames = nilName();
  top.tileNames = top.tileInnerNamesIn;
  top.tileTransformation = nullTransformation(location=builtin);
}

-- unrollTrans
aspect production forIterStmt
top::IterStmt ::= bty::BaseTypeExpr mty::TypeModifierExpr n::Name cutoff::Expr body::IterStmt
{
  local numIters::Integer =
    case cutoff.integerConstantValue of
    | just(n) -> n
    | nothing() -> 1 -- Error when cutoff isn't constant, copy body once to catch further errors
    end;
    
  top.unrollErrors =
    if n.name == top.target.name
    then
      case cutoff.integerConstantValue of
      | just(n) -> []
      | nothing() -> [err(top.target.location, "Unrolled loop must have constant cutoff")]
      end
    else body.unrollErrors;

  top.unrollTrans = 
    if n.name == top.target.name
    then compoundIterStmt(unrollBody(bty, mty, n, body, numIters))
    else forIterStmt(bty, mty, n, cutoff, body.unrollTrans);
}

function unrollBody
IterStmt ::= bty::BaseTypeExpr mty::TypeModifierExpr n::Name body::IterStmt numIters::Integer
{
  local step::IterStmt =
    compoundIterStmt(
      seqIterStmt(
        stmtIterStmt(
          declStmt( 
            variableDecls(
              nilStorageClass(), nilAttribute(),
              bty,
              consDeclarator(
                declarator(
                  n, mty, nilAttribute(),
                  justInitializer(
                    exprInitializer(mkIntExpr(toString(numIters - 1), builtin)))),
                nilDeclarator())))),
        body));

  return
    if numIters > 1
    then seqIterStmt(unrollBody(bty, mty, n, body, numIters - 1), step)
    else if numIters == 1
    then step
    else nullIterStmt();
}

-- parallelizeTrans
aspect production forIterStmt
top::IterStmt ::= bty::BaseTypeExpr mty::TypeModifierExpr n::Name cutoff::Expr body::IterStmt
{
  top.isParallel = body.isParallel;

  top.parallelizeErrors =
    (if top.inParallel
     then [wrn(top.target.location, n.name ++ " is already within a parallel section, parallelizing will have no effect")]
     else []) ++ 
    (if body.isParallel
     then [wrn(top.target.location, n.name ++ " contains a parallel section that will be hidden")]
     else []) ++ body.parallelizeErrors;
  
  top.parallelizeTrans = 
    if n.name == top.target.name
    then parallelForIterStmt(top.numThreads, bty, mty, n, cutoff, body.parallelizeTrans)
    else forIterStmt(bty, mty, n, cutoff, body.parallelizeTrans);
}

-- vectorizeTrans
aspect production forIterStmt
top::IterStmt ::= bty::BaseTypeExpr mty::TypeModifierExpr n::Name cutoff::Expr body::IterStmt
{
  top.isVector = body.isVector;

  top.vectorizeErrors =
    (if top.inVector
     then [err(top.target.location, n.name ++ " is already within a vector section and cannot be vectorized")]
     else []) ++ 
    (if top.isVector
     then [err(top.target.location, n.name ++ " contains a vector section and cannot be vectorized")]
     else []) ++ 
    (if body.isParallel
     then [wrn(top.target.location, n.name ++ " contains a parallel section and cannot be vectorized")]
     else []) ++ body.vectorizeErrors;
  
  top.vectorizeTrans = 
    if n.name == top.target.name
    then vectorForIterStmt(bty, mty, n, cutoff, body.vectorizeTrans)
    else forIterStmt(bty, mty, n, cutoff, body.vectorizeTrans);
}
