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
  ; mk_instance_name : string -> string
  }.

Definition o0 :=
  {| debug := false
   ; mk_instance_name := fun s => "Serialize_" ++ s
  |}.

Definition enable_debug o :=
  {| debug := true
   ; mk_instance_name := mk_instance_name o
  |}.

Definition serializeConstr (o : options)
    (ctx : context) (cname : ident) (cfields : context) (_ : term)
  : TM term :=
  when (debug o) (tmPrint "XX" ;; print_nf (cname, ctx, cfields)) ;;
  let ctx0 := ctx ,,, cfields in
  let n0 := List.length ctx0 in
  let fix serializeFields acc cfields' cn' :=
      match cfields' with
      | {| decl_type := t0 |} :: ct2 =>
        if isSort t0 then
          serializeFields acc ct2 (S cn')
        else (
          let t1 := lift0 (S cn') t0 in
          let q_constraint :=
            it_mkProd_or_LetIn ctx0 (mkApp q_Serialize t1) in
          when (debug o) (tmPrint 0 ;; print_nf q_constraint) ;;
          q_inst <- tmInferInstanceQ (debug o) None q_constraint ;;
          when (debug o) (tmPrint 1) ;;
          let q_inst' := mkApps q_inst (List.map tRel (rev' (seq 0 n0))) in
          let t := mkApps q_sexp_of [t1; q_inst' ; tRel cn'] in
          serializeFields (t :: acc) ct2 (S cn')
        )
      | [] => tmReturn acc
      end in
  sfields <- serializeFields [] cfields 0 ;;
  q_cname <- tmQuote (ARaw cname) ;;
  tmReturn
    match sfields with
    | [] => q_cname
    | _ :: _ => mkApp q_List (q_list_of_list_q q_sexp (q_cname :: sfields))
    end.

Definition _deriveSerialize
    (o : options) (tyDef : mutual_inductive_body)
    (ctx : context) (q_SA' q_A : term)
  : TM term :=
  if is_recursive tyDef then
    let name_sexp_of := nNamed "_sexp_of" in
    let ctx' := ctx ,, vass name_sexp_of q_SA' ,, vass nAnon (lift0 1 q_A) in
    body <- tMatch (tRel 0) (lift0 2 q_A) q_sexp (serializeConstr o ctx') ;;
    let body :=
      tFix [mkdef _ name_sexp_of (tProd nAnon q_A q_sexp)
                  (tLambda nAnon (lift0 1 q_A) body) 0] 0 in
    tmReturn (it_mkLambda_or_LetIn ctx body)
  else
    let ctx := ctx ,, vass nAnon q_A in
    body <- tMatch (tRel 0) (lift0 1 q_A) q_sexp (serializeConstr o ctx) ;;
    tmReturn (it_mkLambda_or_LetIn ctx body).

Definition deriveSerializeWith (o : options) (SA : Type) : TM unit :=
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
  | tInd i _ | tApp (tInd i _) _ =>
    tyDef <- tmQuoteInductive (inductive_mind i) ;;
    tyOne <- get_ind_body tyDef ;;
    q_body <- _deriveSerialize o tyDef ctx q_SA' q_A ;;
    body <- tmUnquoteTyped SA q_body ;;
    iname <- tmEval all (mk_instance_name o (ind_name tyOne)) ;;
    tmDefinitionRed iname None body ;;
    tmExistingInstance iname;;
    tmReturn tt
  | _ => tmFail "not an inductive"
  end.

Definition deriveSerialize : Type -> TM unit := deriveSerializeWith o0.
