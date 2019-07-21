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

Record options :=
  { debug : bool
  }.

Definition o0 :=
  {| debug := false
  |}.

Definition serializeConstr (o : options)
    (ctx : context) (cname : ident) (cfields : context) (_ : term)
  : TM term :=
  when (debug o) (tmPrint "XX" ;; print_nf (cname, ctx, cfields)) ;;
  let ctx0 := ctx ,,, cfields in
  let n0 := List.length ctx0 in
  let fix serializeFields cfields' cn' :=
      match cfields' with
      | {| decl_type := t0 |} :: ct2 =>
        ts <- serializeFields ct2 (S cn') ;;
        if isSort t0 then
          tmReturn ts
        else (
          let t1 := lift0 (S cn') t0 in
          let q_constraint :=
            it_mkProd_or_LetIn ctx0 (mkApp q_Serialize t1) in
          when (debug o) (tmPrint 0 ;; print_nf q_constraint) ;;
          q_inst <- tmInferInstanceQ None q_constraint ;;
          when (debug o) (tmPrint 1) ;;
          let q_inst' := mkApps q_inst (List.map tRel (rev' (seq 0 n0))) in
          let t := mkApps q_sexp_of [t1; q_inst' ; tRel cn'] in
          tmReturn (t :: ts)
        )
      | [] => tmReturn []
      end in
  sfields <- serializeFields cfields 0 ;;
  q_cname <- tmQuote (ARaw cname) ;;
  tmReturn
    match sfields with
    | [] => q_cname
    | _ :: _ => mkApp q_List (q_list_of_list_q q_sexp (q_cname :: sfields))
    end.

Definition deriveSerialize (o : options) (SA : Type) : TM unit :=
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
  match q_A with
  | tApp (tInd i _) _ =>
    tyDef <- tmQuoteInductive (inductive_mind i) ;;
    if is_recursive tyDef then
      let name_to_sexp := nNamed "_to_sexp" in
      let ctx' := ctx ,, vass name_to_sexp q_SA' ,, vass nAnon (lift0 1 q_A) in
      body <- tMatch (tRel 0) (lift0 2 q_A) q_sexp (serializeConstr o ctx') ;;
      let body :=
        tFix [mkdef _ name_to_sexp (tProd nAnon q_A q_sexp)
                    (tLambda nAnon (lift0 1 q_A) body) 0] 0 in
      let qF := it_mkLambda_or_LetIn ctx body in
      tmUnquote qF >>= tmPrint
    else
      let ctx := ctx ,, vass nAnon q_A in
      body <- tMatch (tRel 0) (lift0 1 q_A) q_sexp (serializeConstr o ctx) ;;
      let qF := it_mkLambda_or_LetIn ctx body in
      tmUnquote qF >>= tmPrint
  | _ => tmFail "not an inductive"
  end.

Run TemplateProgram
  (deriveSerialize o0 (forall A, Serialize A -> Serialize (option A))).

Run TemplateProgram
  (deriveSerialize o0 (forall A, Serialize A -> Serialize (list A))).
