Cérès
=====

Cérès is a Coq library for serialization to S-expressions.

S-expressions
-------------

S-expressions are uniform representations of structured data.

They are an alternative to plain strings as used by `Show` in Haskell and
`Debug` in Rust for example.
S-expressions are more amenable to programmatic consumption, avoiding custom
parsers and enabling flexible formatting strategies.

### Example

This S-expression...

```
(example
  (message "I'm a teapot")
  (code 418))
```

... corresponds to this `sexp atom` in Coq.

```coq
Definition example : sexp atom :=
  [ Raw "example"
  ; [ Raw "message" ; Str "I'm a teapot" ]
  ; [ Raw "code" ; Num 418%Z ]
  ].
```

Usage
-----

Import the main module of the library.

```coq
Require Import Ceres.Ceres.
```

This exports:

- `Ceres.S`: the core definitions for S-expressions.
- `Ceres.Serialize`: the `Serialize` type class.

Other modules in the library:

- `Ceres.S_Format`: format S-expressions as strings.
- `Ceres.String`: general string utilities.

Core definitions
----------------

The type of S-expressions. It is parameterized by the type of atoms.

```coq
Inductive sexp (A : Type) :=
| Atom (a : A)
| List (xs : list (sexp A))
.
```

The library offers a default `atom` type, so that the main S-expression type is
`sexp atom`.

```coq
Definition atom : Set.

(* Constructors *)
Definition Num : Z -> atom.
Definition Str : string -> atom.
Definition Raw : string -> atom.

(* Destructors *)
Definition get_Num : atom -> option Z.
Definition get_Str : atom -> option string.
Definition get_Raw : atom -> option string.

(* Coercion Num : Z >-> atom. *)
(* Coercion Atom : atom >-> sexp. *)
```

Serialization
-------------

Serializers can be defined as instances of the `Serialize` type class.

```coq
Class Serialize (A : Type) : Type :=
  sexp_of : A -> sexp atom.
```

S-expression, and thus serializable types, can be serialized to a `string`.

```coq
Definition string_of {A : Type} `{Serialize A} : A -> string.
```

For numeric types, it is sufficient to define a conversion to `Z`.

```coq
Class Integral (A : Type) : Type :=
  Z_of : A -> Z.

Instance Serialize_Integral (A : Type) : Integral A -> Serialize A.
```

See also
--------

- Real World OCaml, [Chapter 17, Data Serialization with
  S-expressions](https://v1.realworldocaml.org/v1/en/html/data-serialization-with-s-expressions.html).
- [Down with Show!](https://harry.garrood.me/blog/down-with-show-part-3/), a
  blog post by Harry Garrood advocating for using structured representations
  instead of strings.
