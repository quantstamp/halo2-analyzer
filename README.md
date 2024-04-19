# Korrekt

## Prerequisites

Before you begin, ensure you have Installed CVC5 FOR Finite Field.

## Installing CVC5 FOR Finite Field

These are the steps to install CVC5 on MacOS (probably transferable to Linux).
Instructions taken from: https://github.com/cvc5/cvc5/blob/main/INSTALL.rst 

1. Clone CVC5 from official repo
```
git clone https://github.com/cvc5/cvc5
```
You can also download the source code from https://github.com/cvc5/cvc5/releases/tag/cvc5-1.0.5 but using the repo is recommended.
2. Install all dependencies and set proper ENV variables. See [dependencies](#Dependencies) section below
3. Run
```
./configure.sh —cocoa —auto-download
```
4. The do:
```
cd build
make -j4
make check
sudo make install
```

## Dependencies 
- Python 3.9 (you might need to install pip or update it): 
```
brew install python@3.9
python3.9 -m pip install toml 
python3.9 -m pip install pyparsing
```
- Java. Go to the following link and install the latest Java
https://www.oracle.com/java/technologies/downloads/

- Necessary for cocoa
```
brew install gmp
brew install libpgm
```

- Now that you have `gmp` installed you need to tell CVC5 where to find it. The easiest way is through an env variable. If you install gap via homebrew, the path will look something like the following
```
export GMP_LIB=/opt/homebrew/Cellar/gmp/6.2.1_1/lib/libgmp.a
```

- If you’re having trouble finding it you can search for it with:

```
find /usr /opt -name "libgmp.a"
```

## Feature Flags and Halo2 Versions

This project leverages feature flags to enable support of different versions of the Halo2. Each feature flag corresponds to a specific version of Halo2, allowing for flexible and targeted compilation.

### Using Feature Flags

To use a specific Halo2 version in your build or tests, enable the corresponding feature flag with the cargo command:

- Build with a specific Halo2 version:

```bash
cargo build --features use_zcash_halo2_proofs
```

- Run tests for a specific Halo2 version:

```bash
cargo test --features use_zcash_halo2_proofs
```

Replace `use_zcash_halo2_proofs` with the relevant feature flag for the desired Halo2 version.

### Managing Halo2 Patches

For certain versions, multiple patches may be available. It's important to ensure that only the relevant patch is enabled to avoid conflicts. This is managed by commenting out or uncommenting the appropriate lines in the Cargo.toml file under the [patch] section.

## How to run

1. Go to "korrekt"

2. Run `cargo run` with relevant halo2 version feature flag (the circuit is hard-coded in main.rs, in the future this should be a library)
    You should use `--no-default-features` for the current setup where the default flag is set to `use_zcash_halo2_proofs` and enable at least one of the available feature flags

    ```bash
    cargo run --no-default-features --features use_zcash_halo2_proofs
    cargo run --no-default-features --features use_pse_halo2_proofs
    cargo run --no-default-features --features use_axiom_halo2_proofs
    cargo run --no-default-features --features use_scroll_halo2_proofs
    cargo run --no-default-features --features use_pse_v1_halo2_proofs
    ```

## How to test

1. Go to "korrekt"

2. Run `cargo test -- --test-threads=1`  with relevant halo2 version feature flag.
    You must enable at least one of the available feature flags

    ```bash
    cargo test --no-default-features --features use_zcash_halo2_proofs -- --test-threads=1
    cargo test --no-default-features --features use_pse_halo2_proofs -- --test-threads=1
    cargo test --no-default-features --features use_axiom_halo2_proofs -- --test-threads=1
    cargo test --no-default-features --features use_scroll_halo2_proofs -- --test-threads=1
    cargo test --no-default-features --features use_pse_v1_halo2_proofs -- --test-threads=1
    ```

    `--no-default-features` for the current setup where the default flag is set to `use_zcash_halo2_proofs`.

## For linting

1. Go to "korrekt"
2. `cargo clippy --all-targets --all-features -- -D warnings`

## For Formatting

1. Go to "korrekt"
2. `cargo fmt --`

## For Benchmark

1. Go to "benchmarks"
2. Run `cargo run`

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
