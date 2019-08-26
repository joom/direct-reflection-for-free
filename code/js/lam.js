// Implementing metaprogramming for the lambda calculus
// using JavaScript's OOP features

const isString = s => typeof s === 'string' || s instanceof String

class Exp {
  constructor () {
    if (new.target === Exp) {
      throw new TypeError('Cannot construct Exp instances directly')
    }
  }
}

class Var extends Exp {
  constructor (v) {
    super()
    if (isString(v)) {
      this.v = v
    } else {
      throw new TypeError(`Var has to contain a String, not ${v}`)
    }
  }
  show () { return this.v }
}

class StrLit extends Exp {
  constructor (s) {
    super()
    if (isString(s)) {
      this.s = s
    } else {
      throw new TypeError(`StrLit has to contain a String, not ${s}`)
    }
  }
  show () { return JSON.stringify(this.s) }
}

class App extends Exp {
  constructor (e1, e2) {
    super()
    if (e1 instanceof Exp && e2 instanceof Exp) {
      this.e1 = e1
      this.e2 = e2
    } else {
      throw new TypeError(`App has to contain two Exps, not ${e1} and ${e2}`)
    }
  }
  show () { return `(${this.e1.show()}) (${this.e2.show()})` }
}

class Abs extends Exp {
  constructor (v, e) {
    super()
    if (isString(v) && e instanceof Exp) {
      this.v = v
      this.e = e
    } else {
      throw new TypeError(`Abs has to contain a String and an Exp, not ${v} and ${e}`)
    }
  }
  show () { return `(λ ${this.v}. ${this.e.show()})` }
}

var descExp = new Map()
descExp.set(Var,    [{field: "v",  type: String}])
descExp.set(StrLit, [{field: "s",  type: String}])
descExp.set(App,    [{field: "e1", type: Exp},    {field: "e2", type: Exp}])
descExp.set(Abs,    [{field: "v",  type: String}, {field: "e", type: Exp}])

const lams = (xs, e) => xs.reduceRight((acc, v) => new Abs(v, acc), e)
const apps = xs => xs.reduce((e1, e2) => new App(e1, e2))

const names = n => {
  var xs = []
  for (var i = 1; i <= n; i++) {
    xs.push("c" + i)
  }
  return xs
}

const collectAbs = e => {
  var xs = []
  while (e instanceof Abs) {
    xs.push(e.v)
    e = e.e
  }
  return {args: xs, body: e}
}

const spineView = e => {
  var xs = []
  while (e instanceof App) {
    xs.unshift(e.e2)
    e = e.e1
  }
  return {head: e, rest: xs}
}

// Scott encoding for any given type's description
const bridgeFromDesc = desc =>
  ({reify: x => {
      let cs = names(desc.size)
      let c = cs[Array.from(desc.keys()).findIndex(e => e == x.constructor)]
      var args = desc.get(x.constructor)
                   .map(o => descLookup.get(o.type).reify(x[o.field]))
      args.unshift(new Var(c))
      return lams(cs, apps(args))
    },
    reflect: e => {
      let {args, body} = collectAbs(e)
      if (args.length !== desc.size) return null
      let {head, rest} = spineView(body)
      if (! head instanceof Var) return null
      let cs = names(desc.size)
      let i = cs.indexOf(head.v)
      let ctor = Array.from(desc.keys())[i]
      let fields = desc.get(ctor)
      if (rest.length !== fields.length) return null
      let arr = rest.map((x, i) => descLookup.get(fields[i].type).reflect(x))
      return new ctor(...arr)
    }
  })

var descLookup = new Map()
descLookup.set(String, { reify:   s => new StrLit(s),
                         reflect: e => e instanceof StrLit ? e.s : null })
descLookup.set(Exp, bridgeFromDesc(descExp))

const id = new Abs("x", new Var("x"))
const k = new Abs("x", new Abs("y", new Var("x")))
const z = new Abs("f", new Abs("x", new Var("x")))
const sz = new Abs("f", new Abs("x", new App(new Var("f"), new Var("x"))))

console.log(descLookup.get(Exp).reflect(descLookup.get(Exp).reify(id)))
