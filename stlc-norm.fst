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
(* | R_bool : e:exp -> typing empty e TBool -> halts e -> red TBool e *)
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
                
val value_normal : v:exp{is_value v} -> halts v
let value_normal v = match v with ELam _ _ -> ExIntro v (Multi_refl v)
                
val red_halts : #t:typ -> #e:exp -> red t e -> Tot (halts e)
let red_halts t e h = match h with R_arrow _ _ _ hh _ -> hh
                                                           
val red_typable_empty : #t:typ -> #e:exp -> red t e -> Tot (typing empty e t) 
let red_typable_empty t e h = match h with | R_arrow k1 k2 ht k3 k4 -> ht

val step_deterministic : e:exp -> e':exp -> e'':exp -> step e e' -> step e e'' -> Lemma (e' = e'')
let rec step_deterministic e e' e'' step1 step2 = 
  match step1, step2 with
  | SApp1 #fe1 fe2 #fe1' fstep_e1, SApp1 #se1 se2 #se1' sstep_e1 ->
     step_deterministic fe1 fe1' se1' fstep_e1 sstep_e1
  | _ -> admit()
									    
(*
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

val step_preserves_red : e:exp -> e':exp -> step e e' -> t:typ -> red t e -> Tot (red t e') (decreases t)         
let rec step_preserves_red e e' s_e_e' t h =
  match t with
  | TArr t1 t2 ->
     match h with R_arrow t1 t2 ty_e h_e f ->
       let has_typ_e' : (typing empty e' t) = preservation s_e_e' ty_e in
       let p : (halts e') = match (step_preserves_halting e e' s_e_e') with Conj pa pb -> pa h_e in
       let ff : (e'':exp -> red t1 e'' -> Tot (red t2 (EApp e' e''))) =
         fun e'' red_t1_e'' -> let h' : (red t2 (EApp e e'')) = f e'' red_t1_e'' in
                               step_preserves_red (EApp e e'') (EApp e' e'') (SApp1 e'' s_e_e') t2 h'  in

       R_arrow t1 t2 has_typ_e' p ff
                            
val steps_preserves_red : e:exp -> e':exp -> b:steps e e' -> t:typ -> red t e -> Tot (red t e')     (decreases b)
let rec steps_preserves_red e e' st_e_e' t h = 
  match st_e_e' with
  | Multi_refl e''1 -> h
  | Multi_step e1 e'' e'1 s_e_e'' st_e''_e' -> 
     steps_preserves_red e'' e' st_e''_e' t (step_preserves_red e e'' s_e_e'' t h)
               
val step_preserves_red' : e:exp -> e':exp -> step e e' -> t:typ -> typing empty e t -> red t e' -> Tot (red t e) (decreases t)         
let rec step_preserves_red' e e' s_e_e' t ty_t h =
   match t with
  | TArr t1 t2 ->
     match h with R_arrow t1 t2 ty_e h_e f ->
       let p : (halts e) = match (step_preserves_halting e e' s_e_e') with Conj pa pb -> pb h_e in
       let ff : (e'':exp -> red t1 e'' -> Tot (red t2 (EApp e e''))) =
         fun e'' red_t1_e'' -> let h' : (red t2 (EApp e' e'')) = f e'' red_t1_e'' in
                               let ty_e'' : (typing empty e'' t1) = red_typable_empty red_t1_e'' in
                               let ty_app : (typing empty (EApp e e'') t2) = (TyApp ty_t ty_e'') in
                               step_preserves_red' (EApp e e'') (EApp e' e'') (SApp1 e'' s_e_e') t2 ty_app h'
       in

       R_arrow t1 t2 ty_t p ff

val steps_preserves_red' : e:exp -> e':exp -> steps e e' -> t:typ -> typing empty e t -> red t e' -> Tot (red t e) (decreases t)         
let rec steps_preserves_red' e e' s_e_e' t ty_t h = admit()

type red2 (g:env) (sigma:sub) =
    (forall x t. g x = Some t ==> (exists e. sigma x = e /\ red t e)) /\
    (forall x e. sigma x = e /\ EVar x <> e ==> (exists t. g x = Some t /\ red t e))
                
(* Definition R' (Gamma:ctx) (theta:sub) : Prop := *)
(* (forall x S, Gamma x = Some S -> exists s, theta x = Some s /\ R S s) *)
(* /\ *)
(* (forall x s, theta x = Some s -> exists S, Gamma x = Some S /\ R S s). *)                                                         
(* type closed2 (sigma:sub) = (forall x e.sigma x = e /\ x <> e ==> closed e) *)

(* val red_closed2 : sigma:sub -> g:env -> red2 g sigma -> Tot (closed'                              *)

(* Lemma R_implies_closed': forall theta Gamma, *)
(*   R' Gamma theta -> closed' theta.                              *)

val red_subst : g:env -> e:exp -> t:typ -> sigma:sub ->
                typing g e t ->
                red2 g sigma ->
                typing empty (subst sigma e) t
let red_subst g e t sigma ty_t r = admit()
  
val main :
      #x:var -> #e:exp -> #t:typ -> #t':typ -> #v:exp -> #g:env ->
      sigma:sub{red2 g sigma} ->                                        
      typing g e t ->
      red t (subst sigma e)
let main = admit()          

let id (x : var) = EVar x

(* val red2_id_empty : Lemma (red2 empty id)                         *)

assume val subst_id : e:exp -> Lemma (subst id e = e)                        
          
val normalization :
      #e:exp -> #t:typ ->
      typing empty e t ->
      halts e
let normalization e t ty = subst_id e; red_halts (main id ty)       
 *)
