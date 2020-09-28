# 0.3.0

- Add `Serialize` and `Deserialize` instances for `ascii`
- Prove roundtrip properties

    + Parser (string -> sexp): parse-then-print roundtrip (soundness; see `CeresParserRoundtrip`)
    + Serializers (sexp <-> mytype): both ways (see `CeresRoundtrip`, exported by default)

# 0.2.0

- Add decidable equality

# 0.1.0

- Create coq-ceres.
