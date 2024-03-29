grammar edu:umn:cs:melt:exts:ableC:halide:abstractsyntax;

inherited attribute iterStmtIn::IterStmt;
synthesized attribute iterStmtOut::IterStmt;

tracked nonterminal Transformation with pp, errors, iterStmtIn, iterStmtOut, env, 
  controlStmtContext;

propagate controlStmtContext on Transformation;

abstract production nullTransformation
top::Transformation ::= 
{
  propagate errors;
  top.pp = notext();
  top.iterStmtOut = top.iterStmtIn;
}

abstract production seqTransformation
top::Transformation ::= h::Transformation t::Transformation
{
  propagate env;
  top.pp = ppConcat([h.pp, line(), t.pp]);
  top.errors := if !null(h.errors) then h.errors else t.errors;
  
  thread iterStmtIn, iterStmtOut on top, h, t, top;
}

abstract production splitTransformation
top::Transformation ::= n::Name iv::IterVar ivs::IterVars
{
  propagate errors;
  top.pp = pp"split ${n.pp} into (${iv.pp}, ${ivs.pp});";
  
  top.errors <-
    if !null(iterStmt.errors)
    then iterStmt.errors
    else if !null(n.valueLookupCheck)
    then [errFromOrigin(n, n.name ++ " is not a transformable loop")]
    else [];
  
  n.env = addEnv(iterStmt.iterDefs, emptyEnv()); -- Env for name lookup consists of only the transformable loop variables
  iv.env = top.env;
  ivs.env = top.env;
 
  local iterStmt::IterStmt = top.iterStmtIn;
  iterStmt.target = n;
  iterStmt.newIterVar = iv;
  iterStmt.newIterVars = ivs;
  iterStmt.env = top.env;
  iterStmt.controlStmtContext = top.controlStmtContext;
  
  top.iterStmtOut = iterStmt.splitTrans;
}

abstract production anonSplitTransformation
top::Transformation ::= n::Name ivs::IterVars
{
  top.pp = pp"split ${n.pp} into (_, ${ivs.pp});";

  local iterStmt::IterStmt = top.iterStmtIn;
  iterStmt.env = top.env;
  iterStmt.controlStmtContext = top.controlStmtContext;
  
  n.env = addEnv(iterStmt.iterDefs, emptyEnv());
  
  forwards to
    splitTransformation(
      n,
      iterVar(
        directTypeExpr(n.valueItem.typerep),
        baseTypeExpr(),
        name("_iter_var_" ++ toString(genInt()))),
      ivs);
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
  iterStmt.controlStmtContext = top.controlStmtContext;
  
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
    if !null(iterStmt.errors)
    then iterStmt.errors
    else if !null(ns.loopLookupChecks)
    then ns.loopLookupChecks
    else if !null(iterStmt.reorderErrors)
    then iterStmt.reorderErrors
    else forward.errors;
  top.errors <- 
    if ns.count != length(sizes)
    then [errFromOrigin(top, s"Incorrect tile dimension: Expected ${toString(ns.count)}, got ${toString(length(sizes))}")]
    else [];
  
  ns.tileSize = sizes;
  ns.tileInnerNamesIn = ns.tileInnerNames;
  ns.env = addEnv(iterStmt.iterDefs, emptyEnv());
  
  -- Decorate iterStmtIn to check loops are contiguous before splitting loops and reordering via forward
  local iterStmt::IterStmt = top.iterStmtIn;
  iterStmt.targets = ns;
  iterStmt.env = top.env;
  iterStmt.controlStmtContext = top.controlStmtContext;
  
  forwards to
    seqTransformation(
      ns.tileTransformation,
      reorderTransformation(ns.tileNames));
}

abstract production unrollTransformation
top::Transformation ::= n::Name
{
  top.pp = pp"unroll ${n.pp};";
  top.errors :=
    if !null(iterStmt.errors)
    then iterStmt.errors
    else if !null(n.valueLookupCheck)
    then [errFromOrigin(n, n.name ++ " is not a transformable loop")]
    else [];
  top.errors <- iterStmt.unrollErrors;
  
  n.env = addEnv(iterStmt.iterDefs, emptyEnv());
  
  local iterStmt::IterStmt = top.iterStmtIn;
  iterStmt.target = n;
  iterStmt.env = top.env;
  iterStmt.controlStmtContext = top.controlStmtContext;
  
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
    else if !null(n.valueLookupCheck)
    then [errFromOrigin(n, n.name ++ " is not a transformable loop")]
    else [];
  top.errors <- iterStmt.parallelizeErrors;
  
  n.env = addEnv(iterStmt.iterDefs, emptyEnv());
  
  local iterStmt::IterStmt = top.iterStmtIn;
  iterStmt.target = n;
  iterStmt.inParallel = false;
  iterStmt.inVector = false;
  iterStmt.numThreads = numThreads;
  iterStmt.env = top.env;
  iterStmt.controlStmtContext = top.controlStmtContext;
  
  top.iterStmtOut = iterStmt.parallelizeTrans;
}

abstract production vectorizeTransformation
top::Transformation ::= n::Name
{
  top.pp = pp"vectorize ${n.pp};";
  top.errors :=
    if !null(iterStmt.errors)
    then iterStmt.errors
    else if !null(n.valueLookupCheck)
    then [errFromOrigin(n, n.name ++ " is not a transformable loop")]
    else [];
  top.errors <- iterStmt.vectorizeErrors;
  
  n.env = addEnv(iterStmt.iterDefs, emptyEnv());
  
  local iterStmt::IterStmt = top.iterStmtIn;
  iterStmt.target = n;
  iterStmt.inParallel = false;
  iterStmt.inVector = false;
  iterStmt.env = top.env;
  iterStmt.controlStmtContext = top.controlStmtContext;
  
  top.iterStmtOut = iterStmt.vectorizeTrans;
}

synthesized attribute loopLookupChecks::[Message] occurs on Names;

aspect production consName
top::Names ::= h::Name t::Names
{
  top.loopLookupChecks =
    (if !null(h.valueLookupCheck)
     then [errFromOrigin(h, h.name ++ " is not a transformable loop")]
     else []) ++ t.loopLookupChecks;
}

aspect production nilName
top::Names ::= 
{
  top.loopLookupChecks = [];
}

-- Parameter attributes for various transformations
inherited attribute target::Name occurs on IterStmt;
inherited attribute targets::Names occurs on IterStmt;
inherited attribute newIterVar::IterVar occurs on IterStmt;
inherited attribute newIterVars::IterVars occurs on IterStmt;
inherited attribute insertedTransFn::(IterStmt ::= IterStmt) occurs on IterStmt;
inherited attribute numThreads::Maybe<Integer> occurs on IterStmt;
propagate target, targets, newIterVar, newIterVars, insertedTransFn, numThreads on IterStmt;

-- Functor attributes that perform various transformations
functor attribute splitTrans occurs on IterStmt;
functor attribute reorderTrans occurs on IterStmt;
functor attribute unrollTrans occurs on IterStmt;
functor attribute parallelizeTrans occurs on IterStmt;
functor attribute vectorizeTrans occurs on IterStmt;
propagate splitTrans, reorderTrans, unrollTrans, parallelizeTrans, vectorizeTrans on IterStmt excluding forIterStmt;

-- Monoid attributes to collect errors for various transformations
monoid attribute reorderErrors::[Message] with [], ++ occurs on IterStmt;
monoid attribute unrollErrors::[Message] with [], ++ occurs on IterStmt;
monoid attribute parallelizeErrors::[Message] with [], ++ occurs on IterStmt;
monoid attribute vectorizeErrors::[Message] with [], ++ occurs on IterStmt;
propagate reorderErrors, unrollErrors, parallelizeErrors, vectorizeErrors on IterStmt excluding forIterStmt;

-- Other misc analysis attributes used by various transformations
monoid attribute isParallel::Boolean with false, || occurs on IterStmt;
monoid attribute isVector::Boolean with false, || occurs on IterStmt;
inherited attribute inParallel::Boolean occurs on IterStmt;
inherited attribute inVector::Boolean occurs on IterStmt;
propagate isParallel, isVector on IterStmt;

propagate inParallel on IterStmt excluding parallelForIterStmt, vectorForIterStmt;
aspect production parallelForIterStmt
top::IterStmt ::= numThreads::Maybe<Integer> bty::BaseTypeExpr mty::TypeModifierExpr n::Name cutoff::Expr body::IterStmt
{
  top.isParallel <- true;
  body.inParallel = true;
}

propagate inVector on IterStmt excluding vectorForIterStmt;
aspect production vectorForIterStmt
top::IterStmt ::= bty::BaseTypeExpr mty::TypeModifierExpr n::Name cutoff::Expr body::IterStmt
{
  top.isVector <- true;
  body.inParallel = true;
  body.inVector = true;
}

-- splitTrans
synthesized attribute splitIndexTrans::Expr occurs on IterVars;
inherited attribute splitIndexTransIn::Expr occurs on IterVars;

synthesized attribute outerCutoffTrans::Expr occurs on IterVars;
synthesized attribute outerCutoffConstVal::Maybe<Integer> occurs on IterVars;

aspect production consIterVar
top::IterVars ::= bty::BaseTypeExpr mty::TypeModifierExpr n::Name cutoff::Expr rest::IterVars
{
  attachNote extensionGenerated("ableC-halide");

  top.splitIndexTrans = rest.splitIndexTrans;
  rest.splitIndexTransIn =
    ableC_Expr { $Expr{top.splitIndexTransIn} * $Expr{cutoff} + $Name{n} };
  
  top.outerCutoffTrans = 
    ableC_Expr { $Expr{cutoff} * $Expr{rest.outerCutoffTrans} };
  
  top.outerCutoffConstVal =
    do {
      c :: Integer <- cutoff.integerConstantValue;
      r :: Integer <- rest.outerCutoffConstVal;
      return c * r;
    };
}

aspect production nilIterVar
top::IterVars ::= 
{
  attachNote extensionGenerated("ableC-halide");
  top.splitIndexTrans = top.splitIndexTransIn;
  top.outerCutoffTrans = ableC_Expr { 1 };
  top.outerCutoffConstVal = just(1);
}

aspect production forIterStmt
top::IterStmt ::= bty::BaseTypeExpr mty::TypeModifierExpr n::Name cutoff::Expr body::IterStmt
{
  attachNote extensionGenerated("ableC-halide");

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
              declRefExpr(n),
              cutoff),
            innerBody,
            nullIterStmt())));
  splitTransBody.env = top.env;
  splitTransBody.controlStmtContext = top.controlStmtContext;
  
  local splitIterVars::IterVars = top.newIterVars;
  splitIterVars.splitIndexTransIn = declRefExpr(splitIterVar.iterVarName);
  splitIterVars.forIterStmtBody = splitTransBody.insertTrans;
  splitIterVars.env = top.env;
  splitIterVars.controlStmtContext = top.controlStmtContext;
  
  local splitIterVar::IterVar = top.newIterVar;
  
  splitIterVar.forIterStmtCutoff =
    case cutoff.integerConstantValue, splitIterVars.outerCutoffConstVal of
    | just(n), just(o) -> mkIntConst(1 + (n - 1) / o)
    | _, _ ->
      ableC_Expr {
        // Calculate ceil(cutoff/product of split indices)
        1 + ($Expr{cutoff} - 1) / $Expr{splitIterVars.outerCutoffTrans}
      }
    end;
  splitIterVar.forIterStmtBody = splitIterVars.forIterStmtTrans;

  top.splitTrans = 
    if n.name == top.target.name
    then splitIterVar.forIterStmtTrans
    else forIterStmt(bty, mty, n, cutoff, body.splitTrans);
}

-- insertTrans
strategy attribute insertTrans =
    forIterStmt(id, id, id, id, insertTrans) <+
    rule on IterStmt of s -> s.insertedTransFn(s) end <+
    id -- Required to ensure that insertTrans is total, even though this attribute only occurs on IterStmt
  occurs on IterStmt;
propagate insertTrans on IterStmt;

-- reorderTrans
inherited attribute reorderConstructorsIn::[Pair<String (IterStmt ::= IterStmt)>] occurs on Names;
inherited attribute reorderBaseIterStmtIn::IterStmt occurs on Names;

synthesized attribute reorderConstructors::[Pair<String (IterStmt ::= IterStmt)>] occurs on IterStmt;
synthesized attribute reorderBaseIterStmt::IterStmt occurs on IterStmt;

attribute reorderErrors occurs on Names;
attribute reorderTrans<IterStmt> occurs on Names;

propagate reorderConstructorsIn, reorderBaseIterStmtIn, reorderErrors on Names;

aspect production consName
top::Names ::= h::Name t::Names
{
  attachNote extensionGenerated("ableC-halide");

  local reorderLookupRes::Maybe<(IterStmt ::= IterStmt)> =
    lookup(h.name, top.reorderConstructorsIn);

  top.reorderErrors <-
    case reorderLookupRes of
      just(_) ->
        if contains(h.name, t.names)
        then [errFromOrigin(h, s"Duplicate loop name ${h.name}")]
        else []
    | nothing() -> [errFromOrigin(h, s"Loop ${h.name} is not contiguous")]
    end;
  
  top.reorderTrans = 
    case reorderLookupRes of
      just(fn) -> fn(t.reorderTrans)
    | nothing() -> t.reorderTrans
    end;
}

aspect production nilName
top::Names ::= 
{
  top.reorderTrans = top.reorderBaseIterStmtIn;
}

aspect default production
top::IterStmt ::= 
{
  top.reorderConstructors = [];
  top.reorderBaseIterStmt = top;
}

aspect production forIterStmt
top::IterStmt ::= bty::BaseTypeExpr mty::TypeModifierExpr n::Name cutoff::Expr body::IterStmt
{
  top.reorderConstructors =
    if contains(n.name, top.targets.names)
    then (n.name, forIterStmt(bty, mty, n, cutoff, _)) :: body.reorderConstructors
    else [];
  
  top.reorderBaseIterStmt =
    if contains(n.name, top.targets.names)
    then body.reorderBaseIterStmt
    else top;
  
  local reorderTargets::Names = top.targets;
  reorderTargets.reorderConstructorsIn = top.reorderConstructors;
  reorderTargets.reorderBaseIterStmtIn = top.reorderBaseIterStmt;
  
  top.reorderErrors :=
    if contains(n.name, top.targets.names)
    then reorderTargets.reorderErrors
    else body.reorderErrors;

  top.reorderTrans = 
    if contains(n.name, top.targets.names)
    then reorderTargets.reorderTrans
    else forIterStmt(bty, mty, n, cutoff, body.reorderTrans);
}

-- tileTrans
inherited attribute tileSize::[Integer] occurs on Names;
inherited attribute tileInnerNamesIn::Names occurs on Names;
propagate tileInnerNamesIn on Names;

synthesized attribute tileInnerNames::Names occurs on Names;
synthesized attribute tileNames::Names occurs on Names;
synthesized attribute tileTransformation::Transformation occurs on Names;

aspect production consName
top::Names ::= h::Name t::Names
{
  local innerName::Name = name(h.name ++ "_inner");
  local outerName::Name = name(h.name ++ "_outer");
  
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
            else error("Tile has wrong dimension")),
          nilIterVar())),
      t.tileTransformation);
  
  t.tileSize = tail(top.tileSize);
}

aspect production nilName
top::Names ::= 
{
  top.tileInnerNames = nilName();
  top.tileNames = top.tileInnerNamesIn;
  top.tileTransformation = nullTransformation();
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
    
  top.unrollErrors :=
    if n.name == top.target.name
    then
      case cutoff.integerConstantValue of
      | just(n) -> []
      | nothing() -> [errFromOrigin(top.target, "Unrolled loop must have constant cutoff")]
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
                    exprInitializer(mkIntExpr(toString(numIters - 1))))),
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
  propagate parallelizeErrors;
  top.parallelizeErrors <-
    if top.inParallel
    then [wrnFromOrigin(top.target, n.name ++ " is already within a parallel section, parallelizing will have no effect")]
    else [];
  top.parallelizeErrors <-
    if body.isParallel
    then [wrnFromOrigin(top.target, n.name ++ " contains a parallel section that will be hidden")]
    else [];
  
  top.parallelizeTrans = 
    if n.name == top.target.name
    then parallelForIterStmt(top.numThreads, bty, mty, n, cutoff, body.parallelizeTrans)
    else forIterStmt(bty, mty, n, cutoff, body.parallelizeTrans);
}

-- vectorizeTrans
aspect production forIterStmt
top::IterStmt ::= bty::BaseTypeExpr mty::TypeModifierExpr n::Name cutoff::Expr body::IterStmt
{
  propagate vectorizeErrors;
  top.vectorizeErrors <-
    if top.inVector
    then [errFromOrigin(top.target, n.name ++ " is already within a vector section and cannot be vectorized")]
    else [];
  top.vectorizeErrors <-
    if top.isVector
    then [errFromOrigin(top.target, n.name ++ " contains a vector section and cannot be vectorized")]
    else [];
  top.vectorizeErrors <-
    if body.isParallel
    then [wrnFromOrigin(top.target, n.name ++ " contains a parallel section and cannot be vectorized")]
    else [];
  
  top.vectorizeTrans = 
    if n.name == top.target.name
    then vectorForIterStmt(bty, mty, n, cutoff, body.vectorizeTrans)
    else forIterStmt(bty, mty, n, cutoff, body.vectorizeTrans);
}
