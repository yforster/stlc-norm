module StlcNormalizing

open StlcCbvDbParSubst
open FStar.Constructive

let ok = magic
let ok_a = admit


(*** Facts about substitution and closedness *)
val id : sub
let id (x : var) = EVar x

val subst_id : e:exp -> Lemma (subst id e = e)
let rec subst_id e =
  match e with
  | EVar x -> ()
  | EApp e1 e2 -> subst_id e1; subst_id e2
  | ELam t e -> subst_id e

val update : sub -> var -> exp -> Tot sub
let update s x v y = if y = x then v else s y

type closed (e : exp) = (forall y. not(appears_free_in y e))
type closed2 (sigma:sub) = (forall x. sigma x <> EVar x ==> closed(sigma x))

val closed_app : e1 : exp -> e2:exp -> Lemma (requires (closed (EApp e1 e2))) (ensures (closed e1 /\ closed e2))
let closed_app e1 e2 = ()

val subst_closed : e:exp ->
   Lemma (requires (closed e)) (ensures (forall sigma. subst sigma e = e))
let rec subst_closed e =
  match e with
  | EApp e1 e2 -> closed_app e1 e2; subst_closed e1; subst_closed e2
  | ELam t1 e1 -> admit() (* needs work, or different definition of closedness *)
  | EVar _ -> () (* actually unreachable case, now needed, but it's probably because of silly definition for closed *)

val substitution_lemma' : #g:env -> g':env -> #e:exp -> #t:typ -> sigma:sub ->
                          typing g e t ->
                          (x:var -> t:typ{g x == Some t} -> g'':env -> Pure (typing g'' (sigma x) t)
                                                                            (requires (b2t (sigma x <> EVar x)))
                                                                            (ensures (fun _ -> True))) ->
                          (x:var -> t:typ -> Lemma (requires (g x == Some t /\ sigma x == EVar x))
                                                   (ensures (g' x == Some t))) ->
                          Tot (typing g' (subst sigma e) t)
let rec substitution_lemma' #g g' #e #t sigma ty_g h1 h2 =
  match ty_g with
  | TyVar x -> if sigma x <> EVar x then h1 x t g' else (h2 x t; TyVar x)
  | TyApp #g_ #e1 #e2 ih1 ih2 -> TyApp (substitution_lemma' g' sigma ih1 h1 (fun x t -> h2 x t)) (substitution_lemma' g' sigma ih2 h1 (fun x t -> h2 x t))
  | TyLam #g t1 #e1 #t2 ih1 ->
     TyLam t1 (substitution_lemma' (extend g' 0 t1) (subst_elam sigma) ih1 (ok()) (fun x t -> ok_a()))

val invariance_env : #e:exp -> #t:typ -> g:env -> g':env -> typing g e t ->
  Pure (typing g' e t) (requires (forall x. is_Some (g x) ==> g x == g' x)) (fun _ -> ensures True)
let rec invariance_env #e #t g g' ty_g =
  match ty_g with
  | TyApp ty_arrow ty_arg -> TyApp (invariance_env g g' ty_arrow) (invariance_env g g' ty_arg)
  | TyLam argT ty_ext -> TyLam argT (invariance_env (extend g 0 argT) (extend g' 0 argT) ty_ext)
  | TyVar #g x -> ok()

val invariance_empty : #e:exp -> #t:typ ->
  typing empty e t -> g:env -> Tot ( typing g e t )
let invariance_empty #e #t ty g = invariance_env #e #t empty g ty

val substitution_lemma : #g:env -> g':env -> #e:exp -> #t:typ -> sigma:sub ->
                         typing g e t ->
                         (x:var -> t:typ{g x == Some t} -> Tot (cexists (fun e -> h:(typing empty e t){sigma x == e}))) ->
                         Tot (typing g' (subst sigma e) t)
let rec substitution_lemma #g g' #e #t sigma ty_g h2 =
  substitution_lemma' g' sigma ty_g (fun x t g'' -> match h2 x t with
                                                    | ExIntro s h -> let (u:unit{g x == Some t}) = ok() in
                                                                     invariance_empty h g'')
                      (fun x t -> match h2 x t with | ExIntro s h -> ())

val subst_update : x:var -> v:exp -> e:exp -> sigma:sub{closed2 sigma} ->
                   Lemma (subst_beta v (subst (subst_elam sigma) e) = subst (update (subst_elam sigma) 0 v) e)
let rec subst_update x v e sigma =
  match e with
  | EVar x -> if x > 0 then
                (
                  if (sigma (x-1) <> EVar (x-1)) then
                    (
                      assert(closed (sigma (x-1)));
                      subst_closed (sigma(x-1))
                    )
                  else
                    (
                      ok_a() (* this should hold per definition *)
                    )
                )
  | EApp e1 e2 -> subst_update x v e1 sigma; subst_update x v e2 sigma
  | _ -> admit() (* fiddly *)

(*** Evaluation and halting terms *)

(* type relation (a:Type) = a -> a -> Type *)

(* TODO this loops, filed as #575 *)
(* type multi (a:Type) (r:relation a) : a -> a -> Type = *)
(* | Multi_refl : x:a -> multi a r x x *)
(* | Multi_step : x:a -> y:a -> z:a -> r x y -> multi a r y z -> multi a r x z *)

type multi (a:Type) (r:a -> a -> Type) : a -> a -> Type =
| Multi_refl : x:a -> multi a r x x
| Multi_step : x:a -> y:a -> z:a -> r x y -> multi a r y z -> multi a r x z

type steps : exp -> exp -> Type = fun x y -> multi exp step x y
type halts (e:exp) : Type = cexists (fun e' -> u:(steps e e'){is_value e'})


val value_normal : v:exp{is_value v} -> Tot (halts v)
let value_normal v = match v with | ELam _ _ -> ExIntro v (Multi_refl v)

val step_deterministic : e:exp -> e':exp -> e'':exp -> step e e' -> step e e'' -> Lemma (e' = e'')
let rec step_deterministic e e' e'' step1 step2 =
  match step1 with
  | SApp1 #fe1 fe2 #fe1' fstep_e1 ->
     (match step2 with
      | SApp1 #se1 se2 #se1' sstep_e1 ->
	     assert(fe1 == se1);
	     step_deterministic fe1 fe1' se1' fstep_e1 sstep_e1;
	     step_deterministic se1 fe1' se1' fstep_e1 sstep_e1
      | _ -> ()
     )
  | SApp2 fe1 #fe2 #fe2' fstep_e2 ->
     (match step2 with
      | SApp2 se1 #se2 #se2' sstep_e2 ->
	     assert(fe2 == se2);
	     step_deterministic fe2 fe2' se2' fstep_e2 sstep_e2;
	     step_deterministic se2 fe2' se2' fstep_e2 sstep_e2
      | SApp1 #se1 se2 #se1' sstep_e1 -> ()
      | _ -> ()
     )
  | SBeta argT body arg ->
     (match step2 with
      | SApp2 se1 #se2 #se2' sstep_e2 -> ()
      | SApp1 #fe1 fe2 #fe1' fstep_e -> ()
      | SBeta argT' body' arg' -> ()
     )

val step_preserves_halting : e:exp -> e':exp -> step e e' -> Tot (ciff (halts e) (halts e'))
let rec step_preserves_halting e e' s_e_e' = magic()
(* TODO Unexpected error ... Failure("NYI: eta_expand(Tm_fvar: StlcCbvDbParSubst.step) StlcCbvDbParSubst.step
        might be related to #208 and #417, or a new issue
  let p1 : (halts e -> Tot (halts e')) =
    fun (h : halts e) ->
    match h with | ExIntro v to_v ->
      match to_v with
      | Multi_step e1 e'' e2 s_e_e'' st_e''_v -> step_deterministic e e' e'' s_e_e' s_e_e'';
                                                 ExIntro v st_e''_v
  in let p2 : (halts e' -> Tot (halts e)) =
     fun (h : halts e') ->
     match h with | ExIntro v to_v -> ExIntro v (Multi_step e e' v s_e_e' to_v)
  in
    Conj p1 p2
*)

(*** The relation red *)

(* This has a negative occurrence of R that makes Coq succumb,
although this definition is just fine (the type decreases);
F* should have similar problems as soon as we start checking
for negative occurrences. Hopefully by then we will also have
a solution for this. *)
type red : typ -> exp -> Type =
| R_bool :  #e:exp -> typing empty e TBool -> halts e -> red TBool e
| R_arrow : t1:typ -> t2:typ -> #e:exp ->
            typing empty e (TArr t1 t2) ->
            halts e ->
            (e':exp -> red t1 e' -> Tot (red t2 (EApp e e'))) ->
            red (TArr t1 t2) e
(*
stlc-norm.fst(151,2-151,9) : Error
Constructor "R_arrow" fails the strict positivity check;
 the constructed type occurs "red" occurs to the left of a pure function type

The unavoidable happened, and it's even worse than in other places
since here we really invert red quite a lot. And no, we don't yet have
a solution for this, although there are some ideas around. *)

(* With universes we should have a new solution for this, which is to
   define red recursively. No clue how well this would work at this
   point. Did a bit of progress below. *)

val red' : t:typ -> e:exp -> Tot Type0 (decreases t)
let rec red' t e =
  cand (cand (typing empty e t) (halts e))
  (match t with
   | TBool -> ctrue
   | TArr t1 t2 -> (e':exp -> red' t1 e' -> Tot (red' t2 (EApp e e'))))

(*
assume type red : typ -> exp -> Type
assume val r_bool :  #e:exp -> typing empty e TBool -> halts e -> Tot (red TBool e)
assume val r_arrow : t1:typ -> t2:typ -> #e:exp ->
            typing empty e (TArr t1 t2) ->
            halts e ->
            (e':exp -> red t1 e' -> Tot (red t2 (EApp e e'))) ->
            Tot (red (TArr t1 t2) e)
assume val red_inv : #t:typ -> #e:exp -> h:red t e -> Tot
  (cor (cexists (fun t1 -> (cexists (fun t2 ->
        h:(cand (typing empty e (TArr t1 t2))
          (cand (halts e)
            (e':exp -> red t1 e' ->
                Tot (red t2 (EApp e e'))))){t = TArr t1 t2}))))
      (h:(cand (typing empty e TBool) (halts e)){t = TBool}))

val red_halts_new : #t:typ -> #e:exp -> red t e -> Tot (halts e)
let red_halts_new #t #e h =
  match red_inv h with
  | IntroL (ExIntro _ (ExIntro _ (Conj _ (Conj h _)))) -> h
  | IntroR (Conj _ hh) -> hh
 *)

val red_halts : #t:typ -> #e:exp -> h:(red t e) -> Tot (halts e)
let red_halts #t #e h =
  match h with
  | R_arrow _ _ _ hh _ -> hh
  | R_bool _ hh -> hh

val red'_halts : #t:typ -> #e:exp -> h:(red' t e) -> Tot (halts e)
let red'_halts #t #e h =
  match h with
  | Conj (Conj _ h) _ -> h

val red_typable_empty : #t:typ -> #e:exp -> red t e -> Tot (typing empty e t)
let red_typable_empty #t #e h =
  match h with
  | R_arrow k1 k2 ht k3 k4 -> ht
  | R_bool t_e ht -> t_e

val red'_typable_empty : #t:typ -> #e:exp -> red' t e -> Tot (typing empty e t)
let red'_typable_empty #t #e h =
  match h with
  | Conj (Conj h _) _ -> h

val step_preserves_red : e:exp -> e':exp -> step e e' -> t:typ -> red t e ->
				     Tot (red t e') (decreases t)
let rec step_preserves_red e e' s_e_e' t h =
  match t with
  | TArr t1 t2 ->
     (match h with
      | R_bool t_e ht -> R_bool t_e (red_halts h) (* CH: isn't this an impossible case? *)
      | R_arrow t1 t2 ty_e h_e f ->
	let has_typ_e' : (typing empty e' t) = preservation s_e_e' ty_e in
	let p : (halts e') = match (step_preserves_halting e e' s_e_e') with | Conj pa pb -> pa h_e in
	let ff : (e'':exp -> red t1 e'' -> Tot (red t2 (EApp e' e''))) =
          fun e'' red_t1_e'' -> let h' : (red t2 (EApp e e'')) = f e'' red_t1_e'' in
				step_preserves_red (EApp e e'') (EApp e' e'') (SApp1 e'' s_e_e') t2 h'	in
	R_arrow t1 t2 has_typ_e' p ff)
  | TBool ->
     (match h with
      | R_bool t_e ht ->
	 let has_typ_e' : (typing empty e' t) = preservation s_e_e' t_e in
	 let p : (halts e') =
	   match (step_preserves_halting e e' s_e_e') with
	   | Conj pa pb -> pa ht in
	 R_bool has_typ_e' p )

val step_preserves_red' : e1:exp -> e2:exp -> step e1 e2 -> t:typ -> red' t e1 ->
				     Tot (red' t e2) (decreases t)
let rec step_preserves_red' e1 e2 s t h =
  match h with
  | Conj (Conj h1 h2) h3 ->
    let Conj h2' _ = step_preserves_halting e1 e2 s in
    let h1' = preservation s h1 in
    Conj (Conj h1' (h2' h2)) (
      match t with
      | TArr t1 t2 ->
        (* Take 1 -- could not prove postcondition *)
        (* fun (e'':exp) -> fun (h':red' t1 e'') -> admit() *)

        (*Take 2:*)
        let aux (e3:exp) (h'':red' t1 e3) : Tot (red' t2 (EApp e2 e3)) =

          (* Take 2.1 -- trying eta expansion, "expected a function" for h3, but it's a match *)
          (* let h3' (e3':exp) (hh:red' t1 e3') : Tot (red' t2 (EApp e1 e3')) = h3 e3' hh in *)

          (* Take 2.2 -- trying subtyping and it does the trick *)
          let h3' : e3':exp -> red' t1 e3' -> Tot (red' t2 (EApp e1 e3')) = h3 in
          let h' : (red' t2 (EApp e1 e3)) = h3' (* can't use h3 directly! "expected a function"*) e3 h'' in
          step_preserves_red' (EApp e1 e3) (EApp e2 e3) (SApp1 e3 s) t2 h'
        in aux
      | TBool -> I
    )

val steps_preserves_red : e:exp -> e':exp -> b:steps e e' -> t:typ -> red t e -> Tot (red t e') (decreases b)
let rec steps_preserves_red e e' st_e_e' t h = magic()
(* TODO Error: Unexpected error ... Failure("NYI: eta_expand(Tm_fvar: StlcCbvDbParSubst.step) StlcCbvDbParSubst.step")
let rec steps_preserves_red e e' st_e_e' t h =
  match st_e_e' with
  | Multi_refl e''1 -> h
  | Multi_step e1 e'' e'1 s_e_e'' st_e''_e' ->
     steps_preserves_red e'' e' st_e''_e' t (step_preserves_red e e'' s_e_e'' t h)
*)

val back_step_preserves_red : e:exp -> e':exp -> step e e' -> t:typ -> typing empty e t -> red t e' -> Tot (red t e) (decreases t)
let rec back_step_preserves_red e e' s_e_e' t ty_t h =
   match t with
  | TArr t1 t2 ->
     (match h with | R_arrow t1 t2 ty_e h_e f ->
       let p : (halts e) = match (step_preserves_halting e e' s_e_e') with | Conj pa pb -> pb h_e in
       let ff : (e'':exp -> red t1 e'' -> Tot (red t2 (EApp e e''))) =
         fun e'' red_t1_e'' -> let h' : (red t2 (EApp e' e'')) = f e'' red_t1_e'' in
                               let ty_e'' : (typing empty e'' t1) = red_typable_empty red_t1_e'' in
                               let ty_app : (typing empty (EApp e e'') t2) = (TyApp ty_t ty_e'') in
                               back_step_preserves_red (EApp e e'') (EApp e' e'') (SApp1 e'' s_e_e') t2 ty_app h'
       in

       R_arrow t1 t2 ty_t p ff)
  | TBool ->
     (match h with
      | R_bool t_e ht ->
	 let p : (halts e) = match (step_preserves_halting e e' s_e_e') with | Conj pa pb -> pb ht in
	 R_bool ty_t p
     )

(*** The relations red2 and ered *)

type red2 (g:env) (sigma:sub) =
    cand (x : var -> t : typ{g x == Some t} -> Tot (cexists (fun e -> h:(red t e){sigma x == e})))
         (x : var -> e : exp{sigma x == e /\ EVar x <> e} -> Tot (cexists (fun t -> h:(red t e){g x == Some t})))
type ered (t : typ) (e : exp) = e':exp -> step e e' -> Tot (red t e')

val red_subst : g:env -> e:exp -> t:typ -> sigma:sub ->
                typing g e t ->
                red2 g sigma ->
                Tot (typing empty (subst sigma e) t)
let red_subst g e t sigma ty_t r = substitution_lemma empty sigma ty_t
                                        (fun x t ->
                                         let Conj r1 r2 = r in
                                         let ExIntro s h1 = r1 x t in
                                         ExIntro s (red_typable_empty h1))

assume val typing_closed : #e:exp -> #t:typ -> typing empty e t -> Lemma (closed e)

val red2_preserves_update :
    #g:env -> #sigma:sub -> t':typ -> u:exp -> red t' u ->
    red2 g sigma -> Tot ( red2 (extend g 0 t') (update (subst_elam sigma) 0 u) )
let red2_preserves_update #g #sigma t' u red_u red2_g = ok()
  (* Conj (fun (x:var) (t: typ{extend g 0 t' x == Some t}) -> *)
  (*       if x <> 0 *)
  (*       then *)
  (*         ( *)
  (*           let Conj p1 p2 = red2_g in *)
  (*           assert (extend g 0 t' x == Some t); *)
  (*           assert (g (x-1) == Some t); *)
  (*           let ExIntro e red_e = p1 (x-1) t in *)
  (*           typing_closed (red_typable_empty red_e); *)
  (*           subst_closed e; *)
  (*           assert (sigma(x-1) = e); *)
  (*           assert (update (subst_elam sigma) 0 u x = subst sub_inc (sigma (x-1))); *)
  (*           assert (subst sub_inc (sigma (x-1)) = sigma(x-1)); *)
  (*         p1 (x-1) t *)
  (*         ) *)
  (*       else *)
  (*         ( *)
  (*           assert (extend g 0 t' x = Some t'); *)
  (*           assert (extend g 0 t' x = Some t); *)
  (*           assert (t' == t); *)
  (*           assert (update (subst_elam sigma) 0 u x == u); *)
  (*           let test : h:(red t u){update (subst_elam sigma) 0 u 0 == u} = red_u in *)
  (*           ExIntro u test *)
  (*         ) *)
  (*      ) *)
  (*      (fun (x:var) (e:exp{update (subst_elam sigma) 0 u x == e /\ EVar x <> e}) ->  *)
  (*       if x <> 0 *)
  (*       then *)
  (*         ( *)
  (*           ok() *)
  (*         ) *)
  (*       else *)
  (*         ( *)
  (*           assert (u == e); *)
  (*           assert(extend g 0 t' x == Some t'); *)
  (*           ExIntro t' red_u *)
  (*         ) *)
  (*      ) *)

val red_exp_closed : #t:typ -> e:exp{not (is_value e)} ->
                     typing empty e t ->
                     ered t e ->
                     Tot (red t e)
let red_exp_closed #t e ty_t f =
  let ExIntro e' h = progress ty_t in
  back_step_preserves_red e e' h t ty_t (f e' h)

val red_beta_induction : t1:typ -> t2:typ -> e:exp ->
               typing (extend empty 0 t1) e t2 ->
               (e' : exp -> red t1 e' -> Tot (red t2 (subst_beta e' e))) ->
	       e':exp -> red t1 e' -> v:exp{is_value v} -> steps e' v ->
	       Tot (red t2 (EApp (ELam t1 e) e'))
let rec red_beta_induction t1 t2 e ty_t2 f e' red_e' v steps_e'v = magic()
(* TODO Error: Unexpected error; ... Failure("NYI: eta_expand(Tm_fvar: StlcCbvDbParSubst.step) StlcCbvDbParSubst.step")

let rec red_beta_induction t1 t2 e ty_t2 f e' red_e' v steps_e'v =
  match steps_e'v with
  | Multi_step same_e' e'' same_v step_e'e'' mult_e''v ->
     red_exp_closed #t2 (EApp (ELam t1 e) e') (TyApp (TyLam #empty t1 #e #t2 ty_t2) (red_typable_empty #t1 #e' red_e'))
     (fun exp_e (stp : step (EApp (ELam t1 e) e') exp_e) ->
      ( match stp with
	| SApp2 lambda #same_e' #same_e'' stp_e' ->
	   step_deterministic e' e'' same_e'' step_e'e'' stp_e';
	   assert(exp_e == (EApp (ELam t1 e) e''));
	   assert(multi exp step e'' v == steps e'' v);
	   assert(same_v == v);
	   red_beta_induction t1 t2 e ty_t2 f e'' (step_preserves_red e' e'' step_e'e'' t1 red_e') v (ok())(*mult_e''v*)
	| SBeta same_t1 same_e same_e' -> f e' red_e'
	| _ -> ok() (* the two cases above are exhaustive... *)
      )
     )
  | Multi_refl same_e' -> back_step_preserves_red (EApp (ELam t1 e) e') (subst_beta e' e) (SBeta t1 e e') t2 (TyApp (TyLam #empty t1 #e #t2 ty_t2) (red_typable_empty #t1 #e' red_e')) (f e' red_e')
*)

val red_beta : t1:typ -> t2:typ -> e:exp ->
               typing (extend empty 0 t1) e t2 ->
               (e' : exp -> red t1 e' -> Tot (red t2 (subst_beta e' e))) ->
               e' : exp -> red t1 e' -> Tot (red t2 (EApp (ELam t1 e) e'))
let red_beta t1 t2 e ty_t2 f e' red_e' =
  let ExIntro v steps_e'v = red_halts red_e'
  in red_beta_induction t1 t2 e ty_t2 f e' red_e' v steps_e'v


val red2_closed' : #g : env -> #sigma : sub ->
                   red2 g sigma -> Lemma (closed2 sigma)
let red2_closed' #g #sigma red2_g = ok_a() (* logically, this is trivial
                                              but it needs at least another axiom *)

(*** The main lemma and the final theorem *)

val main :
      e:exp -> #t:typ -> #t':typ -> #g:env -> sigma:sub ->
      red2 g sigma ->
      typing g e t ->
      Tot (red t (subst sigma e))
let rec main e #t #t' #g sigma red2_g ty_t =
  match ty_t with
  | TyVar x ->
     let Conj h1 h2 = red2_g in
     let ExIntro s h = h1 x t in
     h
  | TyApp #g #e1 #e2 h1 h2 ->
     (match main e1 sigma red2_g h1 with
      | R_arrow t1 t2 ty_e ha_e f -> f (subst sigma e2) (main e2 sigma red2_g h2))
  | TyLam #g t1 #e1 #t2 ty_t2 ->
     let b : typing empty (subst sigma e) (TArr t1 t2) = (red_subst g e t sigma  ty_t red2_g) in
     let ex : halts (subst sigma e) = ExIntro (subst sigma e) (Multi_refl (subst sigma e)) in
     let e1' = (subst (subst_elam sigma) e1) in
     let f : (s: exp -> red t1 s -> Tot ( red t2 (EApp (subst sigma e) s) )) =
       (fun s h1 ->
        assert (e == ELam t1 e1);
        assert (subst sigma e == ELam t1 (subst (subst_elam sigma) e1));
        let p : (typing (extend empty 0 t1) (e1') t2) = (match b with | TyLam bla h4 -> h4) in
        let f : (u:exp -> red t1 u -> Tot (red t2 (subst_beta u e1'))) = fun u red_u ->
          red2_closed' red2_g;
          subst_update 0 u e1 sigma;
          assert (subst_beta u e1' = subst (update (subst_elam sigma) 0 u) e1);
          let r : (red2 (extend g 0 t1) (update (subst_elam sigma) 0 u)) = red2_preserves_update t1 u red_u red2_g in
          main e1 (update (subst_elam sigma) 0 u) (r) ty_t2
        in
        red_beta t1 t2 e1' p f s h1
       ) in
       R_arrow t1 t2 #(subst sigma e) b ex (f)


(* This may help to prove the following fact *)
assume val exfalso_quodlibet : unit -> Pure 'a (requires (False)) (ensures (fun _ -> True))

val red2_id_empty : red2 empty id
let red2_id_empty = Conj (fun x e -> exfalso_quodlibet()) (fun x t -> exfalso_quodlibet())

val normalization :
      #e:exp -> #t:typ ->
      typing empty e t ->
      Tot (halts e)
let normalization #e #t ty = magic()
(* TODO Error: Unexpected error ... Failure("NYI: eta_expand(Tm_fvar: StlcCbvDbParSubst.empty) StlcCbvDbParSubst.empty")
let normalization #e #t ty = subst_id e; red_halts (main e id red2_id_empty ty)
*)
