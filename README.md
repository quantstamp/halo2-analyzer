# Korrekt

## How to run

1. Go to "korrekt"
2. Run `cargo run` (the circuit is hard-coded in main.rs, in the future this should be a library)

## How to test

1. Go to "korrekt"
2. Run `cargo test -- --test-threads=1`

## For linting

1. Go to "korrekt"
2. `cargo clippy --all-targets --all-features -- -D warnings`

## For Formatting

1. Go to "korrekt"
2. `cargo fmt --`

## How it works

### Intro to Halo2

When constructing a Halo2 relation, it consists of:

- Gates: a "small" number of (parameterized) constraints between cells.
- Regions: a logical collection of cells with a set of enabled gates (as indicated by the "selectors").

More on this below.

#### Halo2 "Gates"

Calling the Halo2 "Gates" is kind of a misnomer, for multiple reasons:

##### They are very powerful.

Halo2 "gates" are very powerful: they can enforce any number of arbitrary non-deterministic relations.
For instance, the following can be enforced by a single Halo2 gate:

```
a * b * c != 0
```

Using the polynomial:

```
f(a,b,c,d) := (a * b * c) * d - 1
```

Which has an assignment for `d` st. `f(a,b,c,d) = 0` iff `a * b * c != 0`.
Note that the "gate" above has no "output wires".
Note that `d` is not really "an input": it is part of the witness, but in the example above, it cannot be the output of another gate or part of the statement: it's a "gate hint".

##### The circuit topology is restricted.

When describing a "circuit" you can usually wire any output to any input.
This is also possible in Halo2, indeed, the original PlonK paper describes a "universal gate" and a permutation check which enables this (in Halo2 this corresponds to "enabling equality" on the 3 input/output columns).
However, often in Plonkish arithmetization the layout is intentionally restricted: allowing some subset of the wires (columns) to have arbitrary wiring
and restricting the rest to accessing other cells defined only locally.
This is done for efficiency.
An example of when this is useful is the repeated application of a function:

```
y = f(f(f(x))
```

Which can be described as:

```
z1 = f(x)
z2 = f(z1)
y  = f(z2)
```

Note that every application of "f" only accesses the output from the previous application.
Defining a "gate" implementing "f" taking as "input" the "output register" of the previous row,
enables computing repeated applications of "f" without wiring checks.
When "f" is, for instance, the round function of a hash function, a single application of "f" is never used, instead large numbers of consecutive rows will implement the full call to the compression function.

#### How to mess it up

As you can probably see there is ample opportunity to screw this up, e.g.

- Accidentally choosing the wrong offset when defining/using a gate.
- Forgetting to enable a selector, or enabling the wrong selector.

These pit-falls will lead to soundness (not completeness) issues: the proof will still generate and will still be valid.
This problem is much more pronounced with Halo than previous systems e.g. bellman, since witness generation (completeness) is completely independent of constraints (soundness).

### Extracting a description of the relation from Halo2

As outlined above, Halo2 first defines a number of "gates" (which are enabled by selectors), each such "gate" consists of one/more polynomials which can be enforced over regions. Korrekt works by collecting all the gates and regions using a custom implementation (`AnalyticLayouter` of the `Layouter` trait, which normally is responsible for "place-and-route" (similar to the role of PnR in HDLs is responsible for mapping the regions to rows to minimize the number of required rows to enforce the constraints: essentially it solves a packing problem).

In our case, the `Layouter` will simply record the details of every region.

Since we never need to actually generate a proof the actual PnR is not needed.

### Abstractly Evaluating Gates across Regions

At this point we have for every region:

- The set of enabled selectors.
- The assigned cells (but with dummy values)

And the gates:

- A set of polynomials for each gate.

If the "circuit" is satisfied, then every polynomial of every gate should vanish over every region: for gates which are not "enabled" the polynomial is `0 * g(<witness>)`, since the "selector" variable is set to 0, i.e. the gate polynomial is:

```
f(<witness>, selector) = selector * g(<witness>)
```

However, since we do not have a witness we can't evaluate the gate polynomials (also, doing so would always yield 0).

What we do have is the selectors and constants which enables us to *abstractly evaluate* every polynomial of every gate in every region for *concrete* values of selector and constant free variables.

An example is in order:

Suppose we have the following polynomial:

```
f(s,a,b,C) := s * (C * a - b)
```

The variables have the following interpretations:

- `s` is the "selector" (determining if the "gate" is enabled), if it is 0 then the polynomial is always 0.
- `a` is the "input" of the gate.
- `b` is the "output" of the gate.
- `C` is a parameter used to configure the gate: a constant in the circuit.

The "gate" "computes" the following relation: `b = C * a` i.e. it is a "multiplication by constant" gate.

After running synthesis with the `AnalyticalLayouer` we have assignments for `s` and `C` (but not for `a` and `b`),
as such we cannot fully evaluate `f` but we can determine if it is identically zero, i.e. zero for *every* `a` and `b`.
We could so so by enumerating assignments for `a` and `b`, which would be slow and accurate, by using a SAT solver, which would be much faster and accurate, or as presently done using abstract interpretation, which is blazingly fast at the cost of accuracy i.e. may yields _false negatives_:
may return that `f` is not identically zero, when in fact it is.

We introduce the following type:

```rust
pub enum AbsResult {
    Variable,
    NonZero,
    Zero,
}
```

Which represents a polynomial which is either:

1. Something (probably depending on the witness).
2. Definitely *not zero* (for any witness).
3. Definitely *zero* (for any witness).

To see how to generate this consider the simples possible case of a constant:

```rust
pub fn eval_abstract<F: FieldExt>(expr: &Expression<F>, selectors: &HashSet<Selector>) -> AbsResult {
    match expr {
        Expression::Constant(v) => if v.is_zero().into() { AbsResult::Zero } else {  AbsResult::NonZero },
```

The function of the code is pretty self-explanatory. We can do a similar thing for the selectors:


```rust
Expression::Selector(selector) => {
    match selectors.contains(selector) {
        true => AbsResult::NonZero,
        false => AbsResult::Zero
    }
}
```

However for the "advice" (wire assignments), we have to throw up our hands and output "Variable" (meaning it could be anything):

```rust
Expression::Advice { .. } => AbsResult::Variable,
```

We can also calculate with these, e.g. a negation does not affect the zero/non-zero status:

```rust
Expression::Negated(expr)  => {
    let res = eval_abstract(expr, selectors);
    return res
}
```

While a sum operates as follows:

```rust
Expression::Sum(left, right) => {
    let res1 = eval_abstract(left, selectors);
    let res2 = eval_abstract(right, selectors);
    match (res1, res2) {
        (AbsResult::Variable, _) => AbsResult::Variable, // could be anything
        (_, AbsResult::Variable) => AbsResult::Variable, // could be anything
        (AbsResult::NonZero, AbsResult::NonZero) => AbsResult::Variable, // could be zero or non-zero
        (AbsResult::Zero, AbsResult::Zero) => AbsResult::Zero,
        (AbsResult::Zero, AbsResult::NonZero) => AbsResult::NonZero,
        (AbsResult::NonZero, AbsResult::Zero) => AbsResult::NonZero,
    }
}
```

And a multiplication operates as follows:

```rust
Expression::Product(left, right) => {
    let res1 = eval_abstract(left, selectors);
    let res2 = eval_abstract(right, selectors);
    match (res1, res2) {
        (AbsResult::Zero, _) => AbsResult::Zero,
        (_, AbsResult::Zero) => AbsResult::Zero,
        (AbsResult::NonZero, AbsResult::NonZero) => AbsResult::NonZero,
        _ => AbsResult::Variable,
    }
}
 ```

After this process, we have a result indicating whether a polynomial is: definitely zero (trivially satisfied), definitely non-zero (impossible to satisfy) or variable (depending on the witness).
With this simple tool we then proceed to implement a bunch of checks for individual regions described next.

### Checks

#### Unused Gate

Check that for every gate there exists a region in which it is not identically zero.

#### Unconstrained Cell

Check that for every assigned cell in the region, it occurs in a polynomial which is not identically zero over this region.
This means that part of the witness is not constrained -- this is almost certainly a bug.

#### Unused Column

Check that every column occurs in some polynomial.
