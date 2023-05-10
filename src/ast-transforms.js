const bt = require("babel-types");
const invariant = require("invariant");
const t = require("./cljs-types");
const utils = require("./utils");

const jsTypes = require("./ast-types/javascript");
const jsxTypes = require("./ast-types/jsx");

const { globalObj } = utils;

const {
  DEF,
  FN,
  DEFN,
  FN_CALL,
  METHOD_CALL,
  THIS_AS,
  PROP_GET,
  NESTED_PROPS_GET,
  DO,
  IF,
  WHEN,
  COND,
  CASE,
  HICCUP_ELEMENT
} = require("./ast-builders");

const File = (next, ast, opts) => next(ast.program);
const Program = (next, ast, opts) => t.program(ast.body.map(next));
const ExpressionStatement = (next, ast, opts) => next(ast.expression);

const BinaryExpression = (next, ast) => {
  const { operator, left, right } = ast;
  const cljsOp = utils.getBinaryOp(operator);
  if (cljsOp) {
    return t.list([t.symbol(cljsOp), next(left), next(right)]);
  } else {
    throw new Error(`Unsupported binary operator: ${operator}`);
  }
};


const DeleteStatement = (next, ast, opts) => {
  const { argument } = ast;

  invariant(
    bt.isMemberExpression(argument),
    `Can't transform "delete" for non MemberExpression node`
  );

  const prop = next(argument.property);

  invariant(
    prop.value !== undefined || prop.name !== undefined,
    `Couldn't infer "delete" key. Should be a symbol or a number`
  );

  const property =
    prop.type === "StringLiteral"
      ? prop
      : prop.type === "NumericLiteral"
      ? prop
      : t.StringLiteral(prop.name);

  return t.list([t.symbol("js-delete"), next(argument.object), property]);
};

const UnaryExpression = (next, ast, opts) => {
  const { operator, argument } = ast;
  if (operator === "delete") {
    return DeleteStatement(next, ast, opts);
  }
  return t.list([t.symbol(utils.normalizeOperator(operator)), next(argument)]);
};

const Identifier = (next, ast, opts) => {
  if (opts.isGetter) {
    return t.symbol(`-${ast.name}`);
  }
  if (opts.isDotGetter) {
    return t.symbol(`.-${ast.name}`);
  }
  if (opts.isCall) {
    return t.symbol(`.${ast.name}`);
  }
  if (opts.checkGlobal && globalObj.hasOwnProperty(ast.name)) {
    return t.symbol(`js/${ast.name}`);
  }
  return t.symbol(ast.name);
};

const NumericLiteral = (next, ast, opts) => t.NumericLiteral(ast.extra.raw);

//const VariableDeclaration = (next, ast, opts) => next(ast.declarations[0]);
const VariableDeclaration = (next, ast, opts) => {
  if (ast.declarations.length !== 1) {
    throw new Error("VariableDeclaration: Multiple variable declarations are not supported");
  }

  const id = next(ast.declarations[0].id);
  const init = ast.declarations[0].init ? next(ast.declarations[0].init) : t.NumericLiteral(0);
  return t.list([t.symbol("def"), id, t.list([t.symbol("atom"), init])]);
};



const VariableDeclarator = (next, ast, opts) => {
  const { id, init } = ast;

  if (init === null) {
    return DEF(next(id), t.symbol(t.NIL));
  }

  if (bt.isArrowFunctionExpression(init)) {
    const { body, params } = init;
    return DEFN(next, id, params, body);
  }

  return DEF(next(id), next(init, { isVar: true }));
};

// asyncを変換処理するためにfunction修正
const FunctionDeclaration = (next, ast, opts) => {
  const { id, params, body } = ast;
  const isAsync = ast.async;

  if (isAsync) {
    const goBlockBody = bt.blockStatement([
      bt.expressionStatement(
        bt.callExpression(bt.identifier("go"), [bt.arrowFunctionExpression([], body)])
      ),
    ]);
    return DEFN(next, id, params, goBlockBody);
  } else {
    return DEFN(next, id, params, body);
  }
};


const FunctionExpression = (next, ast, opts) => {
  const { id, params, body } = ast;
  const isAsync = ast.async;

  if (isAsync) {
    const goBlockBody = bt.blockStatement([
      bt.expressionStatement(
        bt.callExpression(bt.identifier("go"), [bt.arrowFunctionExpression([], body)])
      ),
    ]);

    if (id === null || opts.isVar) {
      return FN(next, id, params, goBlockBody);
    } else {
      return DEFN(next, id, params, goBlockBody);
    }
  } else {
    if (id === null || opts.isVar) {
      return FN(next, id, params, body);
    } else {
      return DEFN(next, id, params, body);
    }
  }
};


const ArrowFunctionExpression = (next, ast, opts) => {
  const { params, body } = ast;
  return FN(next, null, params, body, { isImplicitDo: !ast.expression });
};

// 下記だとast.argument が null であることを考慮していない。
// const ReturnStatement = (next, ast, opts) => next(ast.argument);

const ReturnStatement = (next, ast, opts) => {
  const { argument } = ast;
  if (argument === null) {
    // 空を返すreturnの変換をスキップ為コメントアウト
    return t.list([t.symbol("return"), t.symbol("nil")]);
    //return t.list([]);
    return null;
  } else {
    return t.list([t.symbol("return"), next(argument)]);
  }
};

const CallExpression = (next, ast, opts) => {
  const { callee } = ast;

  const memberChain = utils.maybeThreadMemberSyntax(next, ast).reverse();
  const isSpreadCall = ast.arguments.some(arg => bt.isSpreadElement(arg));
  const spreadArgs = isSpreadCall
    ? ArrayExpression(next, { elements: ast.arguments }, opts)
    : undefined;

  if (memberChain.length > 2) {
    return t.list([t.symbol("->"), ...memberChain]);
  }

  if (bt.isMemberExpression(callee)) {
    if (callee.object.name && globalObj.hasOwnProperty(callee.object.name)) {
      const fn = t.symbol(`js/${callee.object.name}`);
      if (isSpreadCall) {
        return t.list([
          t.symbol(".apply"),
          t.list([next(callee.property, { isDotGetter: true }), fn]),
          fn,
          spreadArgs
        ]);
      }
      return METHOD_CALL(next, callee.property, fn, ast.arguments);
    } else {
      const fn = next(callee, { isCallExpression: true });
      if (isSpreadCall) {
        const object = fn.children[1];
        return t.list([
          t.symbol(".apply"),
          t.list([next(callee.property, { isDotGetter: true }), object]),
          object,
          spreadArgs
        ]);
      }
      return t.list([...fn.children, ...ast.arguments.map(next)]);
    }
  }
  if (globalObj.hasOwnProperty(callee.name)) {
    const fn = t.symbol(`js/${callee.name}`);
    if (isSpreadCall) {
      return t.list([t.symbol(".apply"), fn, t.symbol(t.NIL), spreadArgs]);
    }
    return FN_CALL(next, fn, ast.arguments);
  }
  if (isSpreadCall) {
    return t.list([
      t.symbol(".apply"),
      next(callee),
      t.symbol(t.NIL),
      spreadArgs
    ]);
  }

  return FN_CALL(next, next(callee), ast.arguments);
};

const MemberExpression = (next, ast, opts) => {
  const { object, property } = ast;

  if (opts.isCallExpression) {
    if (bt.isThisExpression(object)) {
      return THIS_AS("this", [
        METHOD_CALL(next, property, t.symbol("this"), [])
      ]);
    }
    if (ast.computed) {
      return FN_CALL(
        next,
        FN_CALL(next, t.symbol("aget"), [object, property]),
        []
      );
    }
    return METHOD_CALL(next, property, next(object), []);
  }

  if (bt.isThisExpression(object)) {
    return THIS_AS("this", [METHOD_CALL(next, property, t.symbol("this"), [])]);
  }

  if (ast.computed) {
    return FN_CALL(next, t.symbol("aget"), [object, property]);
  }

  const [target, ...props] = utils.getDotProps(ast);

  if (props.length === 1) {
    return PROP_GET(next, props[0], target);
  }

  return NESTED_PROPS_GET(next, target, props);
};

const StringLiteral = (next, ast, opts) => t.StringLiteral(ast.value);

const ArrayExpression = (next, ast, opts) => {
  const { elements } = ast;

  return elements.reduce((ret, el) => {
    if (bt.isSpreadElement(el)) {
      return t.list([t.symbol(".concat"), ret, next(el)]);
    } else {
      ret.children.push(next(el));
      return ret;
    }
  }, t.ArrayExpression([]));
};

const ObjectExpression = (next, ast, opts) => {
  const { properties } = ast;
  return properties.reduce((ret, el) => {
    if (bt.isSpreadProperty(el)) {
      return t.list([t.symbol("js/Object.assign"), ret, next(el)]);
    } else {
      const lastChild = ret.children[ret.children.length - 1];
      if (lastChild && lastChild.type !== "ObjectProperty") {
        ret.children.push(t.ObjectExpression([next(el)]));
      } else {
        ret.children.push(next(el));
      }
      return ret;
    }
  }, t.ObjectExpression([]));
};

const ObjectProperty = (next, ast, opts) =>
  t.ObjectProperty([next(ast.key), next(ast.value)]);

const ThisExpression = (next, ast, opts) => THIS_AS("this", []);

// デフォルト引数に対応できるようにする
const AssignmentPattern = (next, ast, opts) => {
  const left = next(ast.left);
  const right = next(ast.right);
  return t.list([t.symbol("or"), left, right]);
};

/*
const AssignmentExpression = (next, ast, opts) => {
  if (bt.isMemberExpression(ast.left) && ast.left.computed) {
    return t.list([
      t.symbol("aset"),
      next(ast.left.object),
      next(ast.left.property),
      next(ast.right)
    ]);
  }

  const expr = t.list([t.symbol("set!"), next(ast.left), next(ast.right)]);

  if (
    bt.isMemberExpression(ast.left) &&
    utils.isNestedThisExpression(ast.left)
  ) {
    utils.alterNestedThisExpression("that", ast.left);
    return THIS_AS("that", [expr]);
  }
  return expr;
};
*/
const AssignmentExpression = (next, ast, opts) => {
  const { operator, left, right } = ast;
  const leftExpr = next(left);
  const rightExpr = next(right);

  if (operator === '=') {
    return t.list([t.symbol("swap!"), leftExpr, t.symbol("fn"), t.vector([]), rightExpr]);
  } else if (operator === '+=') {
    return t.list([t.symbol("swap!"), leftExpr, t.symbol("fn"), t.vector([]), t.list([t.symbol('+'), t.list([t.symbol('deref'), leftExpr]), rightExpr])]);
  } else {
    throw new Error(`AssignmentExpression: Unsupported operator "${operator}"`);
  }
};



const NewExpression = (next, ast, opts) => t.list([
  t.symbol("new"),
  next(ast.callee, { isCallExpression: !bt.isMemberExpression(ast.callee), checkGlobal: true }),
  ...ast.arguments.map(next)
]);

const ObjectMethod = (next, ast, opts) =>
  t.ObjectProperty([next(ast.key), FN(next, null, ast.params, ast.body)]);

const EmptyStatement = (next, ast, opts) => t.EmptyStatement();

const BlockStatement = (next, ast, opts) => {
  if (bt.isVariableDeclaration(ast.body[0])) {
    const [decls, rest] = utils.takeWhile(
      n => bt.isVariableDeclaration(n),
      ast.body
    );
    const entries = utils.flatMap(d => {
      const { id, init } = d.declarations[0];
      if (init === null) {
        return [next(id), t.symbol(t.NIL)];
      }
      return [next(id), next(init)];
    }, decls);
    const ret = t.list([t.symbol(t.LET), t.vector(entries)]);
    if (rest) {
      ret.children.push(...rest.map(next));
    }
    return ret;
  }
  if (opts.isImplicitDo) {
    return ast.body.map(next);
  }

  return DO(ast.body.map(next));
};

const IfStatement = (next, ast, opts) => {
  const { test, consequent, alternate } = ast;

  if (bt.isIfStatement(alternate)) {
    return COND(next, ast);
  }
  if (alternate !== null) {
    return IF(next, test, consequent, alternate);
  }
  return WHEN(next, test, consequent);
};

const SwitchStatement = (next, ast, opts) => {
  const { discriminant, cases } = ast;
  return CASE(next, discriminant, cases);
};

const SwitchCase = (next, ast, opts) => {
  const { test, consequent } = ast;

  const csqf = consequent.filter(n => !bt.isBreakStatement(n));
  const csq = csqf.map(next);

  if (bt.isVariableDeclaration(consequent[0])) {
    const [decls, rest] = utils.takeWhile(
      n => bt.isVariableDeclaration(n),
      csqf
    );
    const entries = utils.flatMap(d => {
      const { id, init } = d.declarations[0];
      return [next(id), next(init)];
    }, decls);

    return [
      next(test),
      t.list([t.symbol(t.LET), t.vector(entries), ...rest.map(next)])
    ];
  }

  if (test === null) {
    return csq;
  }
  return [next(test), csq.length > 1 ? DO(csq) : csq[0]];
};

const BreakStatement = (next, ast, opts) => t.BreakStatement();

const ImportDeclaration = (next, ast, opts) => {
  const { source, specifiers } = ast;

  const sxs = specifiers.map(s => {
    if (bt.isImportSpecifier(s)) {
      return [next(s.imported, { isDotGetter: true }), next(s.local)];
    }
    if (bt.isImportDefaultSpecifier(s)) {
      return [t.symbol(".-default"), next(s.local)];
    }
    if (bt.isImportNamespaceSpecifier(s)) {
      return ["*", next(s.local)];
    }
  });

  const imported = sxs[0][0];
  const local = sxs[0][1];

  if (imported === "*") {
    return DEF(local, FN_CALL(next, t.symbol("js/require"), [source]));
  }

  return DEF(
    local,
    t.list([imported, FN_CALL(next, t.symbol("js/require"), [source])])
  );
};

const ExportDefaultDeclaration = (next, ast, opts) => {
  const { declaration } = ast;
  return t.list([
    t.symbol("set!"),
    t.list([t.symbol(".-default"), t.symbol("js/exports")]),
    next(declaration)
  ]);
};

const ExportNamedDeclaration = (next, ast, opts) => {
  const declaration = next(ast.declaration);
  const id = declaration.children[1];
  const exporter = t.list([
    t.symbol("set!"),
    t.list([t.symbol(`.-${id.name}`), t.symbol("js/exports")]),
    id
  ]);
  return DO([declaration, exporter]);
};

const ConditionalExpression = (next, ast, opts) => {
  const { test, consequent, alternate } = ast;
  return IF(next, test, consequent, alternate);
};

const LogicalExpression = (next, ast, opts) => {
  const { operator, left, right } = ast;
  return FN_CALL(next, t.symbol(utils.normalizeOperator(operator)), [
    left,
    right
  ]);
};

const NullLiteral = (next, ast, opts) => t.symbol(t.NIL);

const BooleanLiteral = (next, ast, opts) => t.BooleanLiteral(ast.value);

const RegExpLiteral = (next, ast, opts) => t.RegExpLiteral(ast);

const TryStatement = (next, ast, opts) => {
  const { block, handler, finalizer } = ast;
  const body = next(block, { isImplicitDo: true });
  const expr = t.list([t.symbol(t.TRY)]);

  if (Array.isArray(body)) {
    expr.children.push(...body);
  } else {
    expr.children.push(body);
  }

  expr.children.push(t.list([t.symbol(t.CATCH), ...next(handler)]));

  if (finalizer) {
    const finalBody = next(finalizer, { isImplicitDo: true });
    if (Array.isArray(finalBody)) {
      expr.children.push(t.list([t.symbol(t.FINALLY), ...finalBody]));
    } else {
      expr.children.push(t.list([t.symbol(t.FINALLY), finalBody]));
    }
  }
  return expr;
};

const CatchClause = (next, ast, opts) => {
  const { param, body } = ast;

  const catchBody = next(body, { isImplicitDo: true });

  if (Array.isArray(catchBody)) {
    return [t.symbol("js/Object"), next(param), ...catchBody];
  } else {
    return [t.symbol("js/Object"), next(param), catchBody];
  }
};

const ThrowStatement = (next, ast, opts) =>
  t.list([t.symbol(t.THROW), next(ast.argument)]);

const TemplateLiteral = (next, ast, opts) => {
  const { expressions, quasis } = ast;
  const args = quasis.reduce((ret, q, idx) => {
    const s = t.StringLiteral(q.value.raw);
    if (q === quasis[quasis.length - 1]) {
      return ret.concat(s);
    } else {
      return ret.concat([s, next(expressions[idx])]);
    }
  }, []);
  return t.list([t.symbol("str"), ...args]);
};

const DebuggerStatement = (next, ast, opts) =>
  FN_CALL(next, t.symbol("js-debugger"));

const SpreadElement = (next, ast, opts) => next(ast.argument);
const SpreadProperty = (next, ast, opts) => next(ast.argument);

const ArrayPattern = (next, ast, opts) => {
  const { elements } = ast;
  return t.vector(elements.map(el => next(el)));
};

/* ========= JSX ========= */
const JSXExpressionContainer = (next, ast, opts) => next(ast.expression);

const JSXElement = (next, ast, opts) => {
  const attrs = ast.openingElement.attributes;
  return HICCUP_ELEMENT(next, ast.openingElement, attrs, ast.children);
};

const JSXAttribute = (next, ast, opts) =>
  t.MapEntry(next(ast.name), next(ast.value));

const JSXOpeningElement = (next, ast, opts) =>
  next(ast.name, {
    isJSXElement: utils.isComponentElement(ast.name.name)
  });

const JSXIdentifier = (next, ast, opts) =>
  opts.isJSXElement ? t.symbol(ast.name) : t.keyword(ast.name);

const JSXText = (next, ast, opts) =>
  ast.value.trim() !== "" ? t.StringLiteral(ast.value) : t.EmptyStatement();

/*
const ForOfStatement = (next, ast, opts) => {
  const { left, right, body } = ast;

  const bindingLeft = (() => {
    if (bt.isVariableDeclaration(left)) {
      return next(left.declarations[0].id)
    } else {
      return next(left)
    }
  })();

  return t.list([
    t.symbol("doseq"),
    t.vector([bindingLeft, next(right)]),
    next(body)
  ]);
}
*/

// asyncの変換プロセスを追加
const AsyncFunctionDeclaration = (next, ast, opts) => {
  const { id, params, body } = ast;
  const fn = DEFN(next, id, params, body, { isChannel: true });
  return t.list([t.symbol("cljs.core.async/go"), fn]);
};

const AsyncFunctionExpression = (next, ast, opts) => {
  const { id, params, body } = ast;

  if (id === null || opts.isVar) {
    const fn = FN(next, id, params, body, { isChannel: true });
    return t.list([t.symbol("cljs.core.async/go"), fn]);
  } else {
    const fn = DEFN(next, id, params, body, { isChannel: true });
    return t.list([t.symbol("cljs.core.async/go"), fn]);
  }
};

const AsyncArrowFunctionExpression = (next, ast, opts) => {
  const { params, body } = ast;
  const fn = FN(next, null, params, body, { isImplicitDo: !ast.expression, isChannel: true });
  return t.list([t.symbol("cljs.core.async/go"), fn]);
};


// awaitの変換プロセスを追加
const AwaitExpression = (next, ast, opts) => {
  const { argument } = ast;
  return t.list([t.symbol("<!"), next(argument)]);
};

// continue文の変換処理
const ContinueStatement = (next, ast, opts) => {
  if (!opts.inFor) {
    throw new Error("ContinueStatement is not supported outside of a loop");
  }
  return t.list([t.symbol("recur"), opts.continueLabel]);
};


// For文処理
const ForStatement = (next, ast, opts) => {
  const { init, test, update, body } = ast;

  if (init.type === "VariableDeclaration" && init.declarations.length > 1) {
    throw new Error("ForStatement: Multiple variable declarations are not supported");
  }

  const binding = next(init.declarations[0].id);
  const initValue = next(init.declarations[0].init);
  const testExpr = next(test);
  const bodyExpr = next(body);

  return t.list([
    t.symbol("loop"),
    t.vector([binding, initValue]),
    t.list([t.symbol("when"), t.list([t.symbol("<"), binding, testExpr]), 
      t.list([t.symbol("do"), bodyExpr, 
        t.list([t.symbol("if"), t.list([t.symbol("=", update.operator), t.symbol("++")]), 
          t.list([t.symbol("recur"), t.list([t.symbol("inc"), binding])]),
          t.list([t.symbol("recur"), t.list([t.symbol("+"), binding, t.NumericLiteral(1)])])
        ])
      ])
    ])
  ]);
};

// While文処理
const WhileStatement = (next, ast, opts) => {
  const { test, body } = ast;

  const testExpr = next(test);
  const bodyExpr = next(body);

  return t.list([
    t.symbol("while"),
    testExpr,
    t.list([
      t.symbol("do"),
      bodyExpr
    ])
  ]);
};


/*
const UpdateExpression = (next, ast, opts) => {
  const { operator, argument, prefix } = ast;
  if (operator !== "++" && operator !== "--") {
    throw new Error(`UpdateExpression: Unsupported operator "${operator}"`);
  }

  const updatedArgument = next(argument);

  if (prefix) {
    return t.list([t.symbol(operator === "++" ? "+" : "-"), updatedArgument, t.NumericLiteral(1)]);
  } else {
    return t.list([
      t.symbol("let"),
      t.vector([t.symbol("old-value")]),
      updatedArgument,
      t.list([
        t.symbol("do"),
        t.list([
          t.symbol("set!"),
          updatedArgument,
          t.list([t.symbol(operator === "++" ? "+" : "-"), updatedArgument, t.NumericLiteral(1)]),
        ]),
        t.symbol("old-value"),
      ]),
    ]);
  }
};
*/
const UpdateExpression = (next, ast, opts) => {
  const { operator, argument, prefix } = ast;
  if (operator !== "++" && operator !== "--") {
    throw new Error(`UpdateExpression: Unsupported operator "${operator}"`);
  }

  const updatedArgument = next(argument);

  if (prefix) {
    return t.list([t.symbol("swap!"), updatedArgument, t.symbol(operator === "++" ? "inc" : "dec")]);
  } else {
    return t.list([
      t.symbol("let"),
      t.vector([t.symbol("old-value")]),
      t.list([t.symbol("deref"), updatedArgument]),
      t.list([
        t.symbol("do"),
        t.list([
          t.symbol("swap!"),
          updatedArgument,
          t.symbol(operator === "++" ? "inc" : "dec"),
        ]),
        t.symbol("old-value"),
      ]),
    ]);
  }
};


const transforms = {
  File,
  Program,
  ExpressionStatement,
  BinaryExpression,
  UnaryExpression,
  Identifier,
  NumericLiteral,
  VariableDeclaration,
  VariableDeclarator,
  FunctionDeclaration,
  FunctionExpression,
  ArrowFunctionExpression,
  ReturnStatement,
  CallExpression,
  StringLiteral,
  MemberExpression,
  ArrayExpression,
  ObjectExpression,
  ObjectProperty,
  ThisExpression,
  AssignmentPattern, // 追加
  AssignmentExpression,
  NewExpression,
  ObjectMethod,
  EmptyStatement,
  BlockStatement,
  IfStatement,
  SwitchStatement,
  SwitchCase,
  BreakStatement,
  ImportDeclaration,
  ExportDefaultDeclaration,
  ExportNamedDeclaration,
  ConditionalExpression,
  LogicalExpression,
  NullLiteral,
  BooleanLiteral,
  RegExpLiteral,
  TryStatement,
  CatchClause,
  ThrowStatement,
  TemplateLiteral,
  DebuggerStatement,
  SpreadElement,
  SpreadProperty,
  ArrayPattern,
  //ForOfStatement,
  AsyncFunctionDeclaration,
  AsyncFunctionExpression,
  AsyncArrowFunctionExpression,
  AwaitExpression,
  UpdateExpression,
  ContinueStatement,
  ForStatement,
  WhileStatement,
  JSXExpressionContainer,
  JSXElement,
  JSXAttribute,
  JSXOpeningElement,
  JSXIdentifier,
  JSXText
};

if (false) {
  const missingJSTypes = jsTypes.filter(
    t => Object.keys(transforms).includes(t) === false
  );
  const missingJSXTypes = jsxTypes.filter(
    t => Object.keys(transforms).includes(t) === false
  );

  console.warn("Missing JS types", missingJSTypes);
  console.warn("Missing JSX types", missingJSXTypes);
}

module.exports = transforms;
