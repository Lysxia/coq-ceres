Require Import List Arith Ascii String Fin.
Require Import Ceres.Ceres Ceres.TemplateLib.
Require Import MetaCoq.Template.All.
Import ListNotations.
Set Universe Polymorphism.
Set Primitive Projections.

Import TMNotations.

Quote Definition q_Serialize := @Serialize.
Quote Definition q_sexp_of := @sexp_of.
Quote Definition q_sexp := (sexp atom).
Quote Definition q_List := (@List atom).

Definition serializeConstr
    (cname : ident) (ctx : context) (cfields : context) (_ : term)
  : TM term :=
  let n := List.length cfields in
  let ctx0 := ctx ,,, cfields in
  let n0 := List.length ctx0 in
  let fix serializeFields cfields' cn1' :=
      match cfields' with
      | {| decl_type := t0 |} :: ct2 =>
        let cn' := Nat.pred cn1' in
        ts <- serializeFields ct2 cn' ;;
        if isSort t0 then
          tmReturn ts
        else (
          let t1 := lift0 cn1' t0 in
          let q_constraint :=
            it_mkProd_or_LetIn ctx0 (mkApp q_Serialize t1) in
          q_inst <- tmInferInstanceQ None q_constraint ;;
          let q_inst' := mkApps q_inst (List.map tRel (rev' (seq 0 n0))) in
          let t := mkApps q_sexp_of [t1; q_inst' ; tRel cn'] in
          tmReturn (t :: ts)
        )
      | [] => tmReturn []
      end in
  sfields <- serializeFields cfields n ;;
  q_cname <- tmQuote (ARaw cname) ;;
  tmReturn
    match sfields with
    | [] => q_cname
    | _ :: _ => mkApp q_List (q_list_of_list_q q_sexp (q_cname :: sfields))
    end.

Definition deriveSerialize (SA : Type) : TM unit :=
  q_SA <- tmQuote SA ;;
  let '(ctx, q_SA') := decompose_prod_assum [] q_SA in
  name_Serialize <- getName Serialize ;;
  q_A <- match q_SA' with
    | tApp (tConst name _) [a] =>
      assert_else (eq_string name name_Serialize)
        "Expected instance head of the form (Serialize _) (wrong class name)" ;;
      tmReturn a
    | _ => tmFail "Expected instance head of the form (Serialize _)"
    end ;;
  let ctx := ctx ,, vass nAnon q_A in
  body <- tMatch (tRel 0) (lift0 1 q_A) q_sexp
    (fun cname cfields ct => serializeConstr cname ctx cfields ct) ;;
  let qF := it_mkLambda_or_LetIn ctx body in
  tmUnquote qF >>= tmPrint.

Run TemplateProgram
  (deriveSerialize (forall A, Serialize A -> Serialize (option A))).
