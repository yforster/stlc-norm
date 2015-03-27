module StlcNormalizing

open StlcCbvDbParSubst
open Constructive
       
kind Relation (a:Type) = a -> a -> Type
type multi (a:Type) (r:Relation a) : a -> a -> Type =
| Multi_refl : x:a -> multi a r x x
| Multi_step : x:a -> y:a -> z:a -> r x y -> multi a r y z -> multi a r x z
type steps : exp -> exp -> Type = fun x y -> multi exp step x y
type halts (e:exp) : Type = cexists (fun e' -> u:(steps e e'){is_value e'})

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
| R_pair : t1:typ -> t2:typ -> e:exp{typing empty e (TPair t1 t2) ->
           halts e ->
           red t1 (EFst e) ->
           red t2 (ESnd e) ->
           red (TPair t1 t2) e
 *)                
                
val value_normal : v:exp{is_value v} -> Tot (halts v)
let value_normal v = match v with ELam _ _ -> ExIntro v (Multi_refl v)
                
val red_halts : #t:typ -> #e:exp -> red t e -> Tot (halts e)
let red_halts t e h =
  match h with
  | R_arrow _ _ _ hh _ -> hh
  | R_bool _ hh -> hh
                                                           
val red_typable_empty : #t:typ -> #e:exp -> red t e -> Tot (typing empty e t)
let red_typable_empty t e h =
  match h with
  | R_arrow k1 k2 ht k3 k4 -> ht
  | R_bool t_e ht -> t_e

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
let rec step_preserves_halting e e' s_e_e' =
  let p1 : (halts e -> Tot (halts e')) =
    fun (h : halts e) ->
    match h with ExIntro v to_v ->
      match to_v with
      | Multi_step e1 e'' e2 s_e_e'' st_e''_v -> step_deterministic e e' e'' s_e_e' s_e_e'';
                                                 ExIntro v st_e''_v
  in let p2 : (halts e' -> Tot (halts e)) =
     fun (h : halts e') ->
     match h with ExIntro v to_v -> ExIntro v (Multi_step e e' v s_e_e' to_v)
  in                                          
    Conj p1 p2

val step_preserves_red : e:exp -> e':exp -> step e e' -> t:typ -> red t e ->
				     Tot (red t e') (decreases t)
let rec step_preserves_red e e' s_e_e' t h =
  match t with
  | TArr t1 t2 ->
     (match h with
      | R_bool t_e ht -> R_bool t_e (red_halts h) 
      | R_arrow t1 t2 ty_e h_e f ->
	let has_typ_e' : (typing empty e' t) = preservation s_e_e' ty_e in
	let p : (halts e') = match (step_preserves_halting e e' s_e_e') with Conj pa pb -> pa h_e in
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
	     Conj pa pb -> pa ht in
	 R_bool has_typ_e' p )
	       
                            
val steps_preserves_red : e:exp -> e':exp -> b:steps e e' -> t:typ -> red t e -> Tot (red t e') (decreases b)
let rec steps_preserves_red e e' st_e_e' t h = 
  match st_e_e' with
  | Multi_refl e''1 -> h
  | Multi_step e1 e'' e'1 s_e_e'' st_e''_e' -> 
     steps_preserves_red e'' e' st_e''_e' t (step_preserves_red e e'' s_e_e'' t h)
               
val step_preserves_red' : e:exp -> e':exp -> step e e' -> t:typ -> typing empty e t -> red t e' -> Tot (red t e) (decreases t)         
let rec step_preserves_red' e e' s_e_e' t ty_t h =
   match t with
  | TArr t1 t2 ->
     (match h with R_arrow t1 t2 ty_e h_e f ->
       let p : (halts e) = match (step_preserves_halting e e' s_e_e') with Conj pa pb -> pb h_e in
       let ff : (e'':exp -> red t1 e'' -> Tot (red t2 (EApp e e''))) =
         fun e'' red_t1_e'' -> let h' : (red t2 (EApp e' e'')) = f e'' red_t1_e'' in
                               let ty_e'' : (typing empty e'' t1) = red_typable_empty red_t1_e'' in
                               let ty_app : (typing empty (EApp e e'') t2) = (TyApp ty_t ty_e'') in
                               step_preserves_red' (EApp e e'') (EApp e' e'') (SApp1 e'' s_e_e') t2 ty_app h'
       in

       R_arrow t1 t2 ty_t p ff)
  | TBool ->
     (match h with
      | R_bool t_e ht ->
	 let p : (halts e) = match (step_preserves_halting e e' s_e_e') with Conj pa pb -> pb ht in
	 R_bool ty_t p
     )

val steps_preserves_red' : e:exp -> e':exp -> steps e e' -> t:typ -> typing empty e t -> red t e' -> Tot (red t e) (decreases t)         
let rec steps_preserves_red' e e' s_e_e' t ty_t h = admit()

type red2 (g:env) (sigma:sub) =
    cand (x : var -> t : typ -> Tot (cexists (fun e -> h:(red t e){g x == Some t ==> sigma x == e})))
         (x : var -> e : exp -> Tot (cexists (fun t -> h:(red t e){sigma x == e /\ EVar x <> e ==> g x == Some t})))
                
(* Definition R' (Gamma:ctx) (theta:sub) : Prop := *)
(* (forall x S, Gamma x = Some S -> exists s, theta x = Some s /\ R S s) *)
(* /\ *)
(* (forall x s, theta x = Some s -> exists S, Gamma x = Some S /\ R S s). *)
(* type closed2 (sigma:sub) = (forall x e.sigma x = e /\ x <> e ==> closed e) *)

(* val red_closed2 : sigma:sub -> g:env -> red2 g sigma -> Tot (closed'                              *)

(* Lemma R_implies_closed': forall theta Gamma, *)
(*   R' Gamma theta -> closed' theta.                              *)

val substitution_lemma' : #g:env -> g':env -> #e:exp -> #t:typ -> sigma:sub ->
                          typing g e t ->
                          (x:var -> t:typ -> g'':env -> Tot (typing g'' (sigma x) t)
                                                            (requires (g x == Some t /\ sigma x <> EVar x))
                                                            (ensures True)) ->
                          (x:var -> t:typ -> Lemma (requires (g x == Some t /\ sigma x == EVar x))
                                                   (ensures (g' x == Some t))) ->
                          Tot (typing g' (subst sigma e) t)
let rec substitution_lemma' g g' e t sigma ty_g h1 h2 =
  match ty_g with
  | TyVar x -> if sigma x <> EVar x then h1 x t g' else (h2 x t; TyVar x)
  | TyApp #g_ #e1 #e2 ih1 ih2 -> TyApp (substitution_lemma' g' sigma ih1 h1 (fun x t -> h2 x t)) (substitution_lemma' g' sigma ih2 h1 (fun x t -> h2 x t))
  | TyLam #g t1 #e1 #t2 ih1 ->
     let subst_elam : y:var -> Tot (e:exp{renaming sigma ==> is_EVar e}) =
       fun y -> if y=0 then EVar y
                else subst sub_inc (sigma (y-1)) in
     let (u:unit{ (subst sigma (ELam t1 e1) == ELam t1 (subst subst_elam e1)) }) = admit() in
     TyLam t1 (substitution_lemma' (extend g' 0 t1) subst_elam ih1 (h1) h2)

val substitution_lemma : #g:env -> g':env -> #e:exp -> #t:typ -> sigma:sub ->
                         typing g e t ->
                         (x:var -> t:typ -> Tot (cexists (fun e -> h:(typing empty e t){g x == Some t ==> sigma x == e}))) ->
                         Tot (typing g' (subst sigma e) t)
let rec substitution_lemma g g' e t sigma ty_g h2 =                             
  substitution_lemma' g' sigma ty_g (fun x t g'' -> match h2 x t with
                                                      ExIntro s h -> let (u:unit{g x == Some t}) = admit() in
                                                                     typing_extensional h g'')
                      (fun x t -> match h2 x t with ExIntro s h -> ())                      
                      
val red_subst : g:env -> e:exp -> t:typ -> sigma:sub ->
                typing g e t ->
                red2 g sigma ->
                Tot (typing empty (subst sigma e) t)
let red_subst g e t sigma ty_t r = substitution_lemma empty sigma ty_t
                                        (fun x t ->
                                         let Conj r1 r2 = r in
                                         let ExIntro s h1 = r1 x t in
                                         ExIntro s (red_typable_empty h1))

type ered (t : typ) (e : exp) = e':exp -> step e e' -> Tot (red t e')

(* val red_term_ap : t1:typ -> t2:typ -> e:exp{not (is_value e)} -> *)
(*                   (u:exp -> typing empty u t2 -> ered t2 u -> *)
(*                    Tot (red t2 u) (requires (not (is_value u))) (ensures True)) -> *)
(*                   typing empty e (TArr t1 t2) -> *)
(*                   ered (TArr t1 t2) e -> *)
(*                   e':exp -> red t1 e' -> v:exp{is_value v} -> steps e' v -> Tot( red t2 (EApp e e')) *)
(* let red_term_ap t1 t2 e f ty_e ered_e e' red_e' v h =  *)
(*   let rec induction (h : steps e' v) (h4 : red t1 e') : (\* Tot *\) (red t2 (EApp e e')) =  *)
(*     match h with *)
(*     | Multi_refl _ -> magic() *)
(*     | Multi_step e1 e2 e3 s_e_e2 st_e2_e' -> *)
(*        f (EApp e e') (TyApp ty_e (red_typable_empty h4)) *)
(*          (fun u (s_u : step (EApp e e') u) ->  *)
(*           match s_u with *)
(*           | SApp1 e2 #e1 s_e_e1 -> *)
(*              let hh : step e e1 = s_e_e1 in *)
(*              (match ered_e e1 hh with *)
(*                 R_arrow n1 n2 n3 n4 g -> g e' red_e' ) *)
(*           | SApp2 _ _ -> magic() *)
(*          ) *)
(*   in *)
(*   (\* induction h red_e' *\) magic() *)

val red_exp_closed : #t:typ -> #e:exp{not (is_value e)} ->
                     typing empty e t ->
                     ered t e ->
                     Tot (red t e)
let red_exp_closed t e ty_t f =
  let ExIntro e' h = progress ty_t in
  step_preserves_red' e e' h t ty_t (f e' h)

	     

(* val red_beta : t1:typ -> t2:typ -> x:var -> e:exp -> *)
(*                typing (extend empty x t1) e t2 -> *)
(*                (e' : exp -> red t1 e' -> Tot ( red t2 (subst_beta_gen x e' e))) -> *)
(*                e' : exp -> red t1 e' -> red t2 (EApp (ELam t1 e) e') *)
(* let red_beta t1 t2 x e ty_t2 f e' red_e = *)
(*   let ExIntro v h = red_halts red_e in *)
(*   let rec induction ter = *)
(*   match h with *)
(*   | Multi_refl _ -> admit() *)
(*   | Multi_step _ e'' _ s_e'_e'' _ -> admit() in *)
(*   admit() *)
                     
(* val red_preserves_update : g:env -> sigma:sub -> t:typ -> x:var -> e:exp -> *)
(*                            red2 g sigma -> *)
(*                            red t e -> *)
(*                            red2 (extend g x t) (update sigma x t) *)
  
val main :
      #x:var -> #e:exp -> #t:typ -> #t':typ -> #g:env -> sigma:sub ->
      red2 g sigma ->
      typing g e t ->
      Tot (red t (subst sigma e))
let main x e t t' g sigma red2_g ty_t =
  match ty_t with
  | TyVar x ->
     let Conj h1 h2 = red2_g in
     let ExIntro s h = h1 x t in
     h
  | _ -> magic()

val id : sub
let id (x : var) = EVar x
                        
val subst_id : e:exp -> Lemma (subst id e = e)
let rec subst_id e = using_induction_hyp subst_id

val red2_id_empty : red2 empty id
let red2_id_empty = magic()

(* type red2 (g:env) (sigma:sub) = *)
(*     cand (x : var -> t : typ -> 
             Tot (cexists (fun e -> h:(red t e){g x == Some t ==> sigma x == e}))) *)
(*          (x : var -> e : exp -> 
             Tot (cexists (fun t -> h:(red t e){sigma x == e /\ EVar x <> e ==> g x == Some t}))) *)
			 
val normalization :
      #e:exp -> #t:typ ->
      typing empty e t ->
      Tot (halts e)

let normalization e t ty = subst_id e; red_halts (main id red2_id_empty ty)
