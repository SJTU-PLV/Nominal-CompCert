Require Import Coqlib Integers Values Maps AST.
Require Import RelocProg.
Require Import Linking Errors.
Import ListNotations.

Local Open Scope list_scope.

Definition link_symbentry (e1 e2 : symbentry) :=
  match e1.(symbentry_bind),e2.(symbentry_bind) with
  | bind_local,_ => None
  | _,bind_local => None
  | _,_ => match e1.(symbentry_secindex),e2.(symbentry_secindex) with
          | secindex_normal _, secindex_undef => Some e1
          | secindex_undef, secindex_normal _ => Some e2
          | secindex_comm, secindex_undef => Some e1
          | secindex_undef, secindex_comm => Some e2
          | secindex_undef,secindex_undef => Some e1
          | _,_ => None
          end
  end.

Inductive linkorder_symbentry: symbentry -> symbentry -> Prop :=
| linkorder_symbentry_refl: forall e, linkorder_symbentry e e
| linkorder_symbentry_undef_any:
  forall e1 e2, e1.(symbentry_secindex) = secindex_undef ->
           linkorder_symbentry e1 e2.

Program Instance Linker_symbentry : Linker symbentry := {
    link:= link_symbentry;
    linkorder:= linkorder_symbentry
  }.
Next Obligation.
  constructor.
Defined.
Next Obligation.
  inv H;inv H0;try constructor;auto.
Defined.
Next Obligation.
  unfold link_symbentry in H.
  repeat destr_in H;
  split;try constructor;auto.
Defined.

Global Opaque Linker_symbentry.

Definition check_symbentry (e1 e2 : symbentry) :=
  match e1.(symbentry_bind),e2.(symbentry_bind) with
  | bind_local,_ => false
  | _,bind_local => false
  | _,_ => match e1.(symbentry_secindex),e2.(symbentry_secindex) with
          | secindex_normal _, secindex_undef => true
          | secindex_undef, secindex_normal _ => true
          | secindex_comm, secindex_undef =>     true
          | secindex_undef, secindex_comm =>     true
          | secindex_undef,secindex_undef =>     true
          | _,_ => false
          end
  end.

Definition link_section_merge {I D:Type} (o1 o2 : option (section I D)) :=
  match o1,o2 with
  | None,_ => o2
  | _,None => o1
  | Some e1,Some e2 => None
  end.

Definition link_reloctable_merge (o1 o2 : option reloctable) :=
  match o1,o2 with
  | None,_ => o2
  | _,None => o1
  | Some e1,Some e2 => None
  end.

Definition link_reloc_prog (F V I D: Type) (p1 p2: program F V I D) : option (program F V I D) := None.

Program Instance Linker_reloc_prog (F V I D : Type) : Linker (program F V I D) :=
{
  link := (link_reloc_prog F V I D);
  linkorder := fun _ _ => True;
}.

(*** TODO  *)

(* Section LINKER_PROG. *)

(* Context {F V I D: Type} {LF: Linker F} {LV: Linker V} (p1 p2: program F V I D). *)

(* Definition link_relocprog_check (x:ident) (e1: symbentry) := *)
(*   match p2.(prog_symbtable)!x with *)
(*   | Some e2 => check_symbentry e1 e2 *)
(*   | _ => true *)
(*   end. *)


(* Definition link_reloc_prog := *)
(*   let ap1 :=  *)
(*       {| AST.prog_defs   := prog_defs p1; *)
(*          AST.prog_public := prog_public p1; *)
(*          AST.prog_main   := prog_main p1; |} in *)
(*   let ap2 :=  *)
(*       {| AST.prog_defs   := prog_defs p2; *)
(*          AST.prog_public := prog_public p2; *)
(*         AST.prog_main   := prog_main p2; |} in *)
(*   match link ap1 ap2 with *)
(*   | None => None *)
(*   | Some ap => *)
(*       if PTree_Properties.for_all p1.(prog_symbtable) link_relocprog_check then *)
(*         Some {| prog_defs := PTree.elements (PTree.combine link_prog_merge (PTree_Properties.of_list p1.(prog_defs)) (PTree_Properties.of_list p2.(prog_defs))); *)
(*                prog_public := p1.(prog_public) ++ p2.(prog_public);     *)
(*                prog_main := p1.(prog_main);            *)
(*                prog_sectable := PTree.combine link_section_merge p1.(prog_sectable) p2.(prog_sectable); *)
(*                prog_symbtable := PTree.combine link p1.(prog_symbtable) p2.(prog_symbtable); *)
(*                prog_reloctables := PTree.combine link_reloctable_merge p1.(prog_reloctables) p2.(prog_reloctables); *)
(*                prog_senv := Globalenvs.Genv.to_senv (Globalenvs.Genv.globalenv ap); |} *)
(*       else None *)
(*     end. *)
    
