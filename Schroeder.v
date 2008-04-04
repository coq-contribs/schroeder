(* This program is free software; you can redistribute it and/or      *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2.1   *)
(* of the License, or (at your option) any later version.             *)
(*                                                                    *)
(* This program is distributed in the hope that it will be useful,    *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of     *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the      *)
(* GNU General Public License for more details.                       *)
(*                                                                    *)
(* You should have received a copy of the GNU Lesser General Public   *)
(* License along with this program; if not, write to the Free         *)
(* Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA *)
(* 02110-1301 USA                                                     *)


(* Contribution to the Coq Library   V6.3 (July 1999)                    *)
(****************************************************************************)
(*                 The Calculus of Inductive Constructions                  *)
(*                                                                          *)
(*                                Projet Coq                                *)
(*                                                                          *)
(*                     INRIA                        ENS-CNRS                *)
(*              Rocquencourt                        Lyon                    *)
(*                                                                          *)
(*                                Coq V5.11                                 *)
(*                              Feb 2nd 1996                                *)
(*                                                                          *)
(****************************************************************************)
(*                               Schroeder.v                                *)
(****************************************************************************)


(*     If A is of cardinal less than B and conversely, then A and B          *)
(*       are equipollent                                                     *)
(*     In other words, if there is an injective map from A to B and          *)
(*   an injective map from B to A then there exists a map from A onto B.     *)

(*                (d'apres une demonstration de Fraenkel)                    *)

Require Import Ensembles.      (* Ensemble, In, Included, Setminus *)
Require Import Relations_1.    (* Relation, Transitive *)
Require Import Powerset.       (* Inclusion_is_transitive *)
Require Import Classical_Prop. (* classic *)

Require Import Setminus_fact.
Require Import Sums.
Require Import Functions.
Require Import Equipollence.

Section Schroeder_Bernstein.


(*****************************************************************************)
(* We need the decidability of the belonging relation on sets                *)
(* This is equivalent to classical logic                                     *)

Definition in_or_not_in (U : Type) (x : U) (A : Ensemble U) :=
  classic (In U A x).


(*****************************************************************************)
(*  A and B are sets of elements in the univers U                            *)


Variable U : Type.

Let SU := Ensemble U.

Variable A B : SU.  (* A et B sont des ensembles d'elements de l'univers U  *)


  Section Bijection.

  (**************************************************************************)
  (* On montre dans ce paragraphe que si f et g sont des injections resp    *)
  (* de A dans B et de B dans A alors on peut trouver un sous-ensemble J de *)
  (* A tq h qui est f sur J et g sur A\J est une bijection de A dans B      *)

  Variable f g : Relation U.  (* f et g sont des relations *)

  Hypothesis f_inj : injection U A B f. (* f et g sont des injections *)
  Hypothesis g_inj : injection U B A g.

  Let Imf : Ensemble U -> Ensemble U := Im U f.
  Let Img : Ensemble U -> Ensemble U := Im U g.

  (* Construction de J tq g(B\f(J))=A\J *)

    (* (Setminus U A C) designe la difference A\C         *)
    (* (Included U A C) signifie que A est inclus dans C  *)

    Let F (C : SU) := Setminus U A (Img (Setminus U B (Imf C))).

    Let D (C : SU) := Included U C (F C).

    Let J := Set_Sum U D.


  (*  On va montrer que J correspond a ce que l'on cherche *)

    (* J correspond exactement au point fixe de Tarski pour F, *)
    (* fonction croissante relativement a l'inclusion          *)

    (* Lemma F est croissante *)

      Lemma  (* Remark *) F_croissante :
       forall C C' : SU, Included U C C' -> Included U (F C) (F C').
        intros; unfold F in |- *.
        apply Setminus_contravariant.
        unfold Img in |- *.
        apply Im_stable_par_incl.
        apply Setminus_contravariant.
        unfold Imf in |- *.
        apply Im_stable_par_incl.
        assumption.
      Qed.

    (* On va montrer que F(J)=A\Img(B\Imf(J))=J *)

       (* D'abord l'inclusion dans un sens *)

         (*  Lemma J_dans_FJ (Included U J (F J))  *)

         Lemma  (* Remark *) J_dans_FJ : Included U J (F J).
           unfold J in |- *.
           apply Set_Sum_is_majoring.
           intros C C_in_D.
           cut (Transitive (Ensemble U) (Included U)).
             2: apply Inclusion_is_transitive.
           intro Incl_is_trans.
           unfold Transitive in Incl_is_trans.
           apply Incl_is_trans with (F C).
           (* Que C est inclus dans (F C) *)
             assumption.
           (* Que (F C) inclus dans (F (Set_Sum U D)) *)
             apply F_croissante.
             apply Set_Sum_is_minoring.
             assumption.
         Qed.

       (* Puis dans l'autre sens *)

         (*  Lemma FJ_dans_J (Included U (F J) J)  *)

         Lemma  (* Remark *) FJ_dans_J : Included U (F J) J.
           unfold J in |- *.
           apply Set_Sum_is_minoring.
           red in |- *.
           red in |- *.
           apply F_croissante.
           exact J_dans_FJ.
         Qed.


  (* On montre que h qui est f sur J et g ailleurs est une bijection *)

    Inductive h (x y : U) : Prop :=
      | hl_intro : In U J x -> f x y -> h x y
      | hr_intro : Setminus U B (Imf J) y -> g y x -> h x y.


  (*  Theorem h_bij (bijection U A B h)     *)

  Theorem h_bij : bijection U A B h.


    (* h est de A dans B *)
    Lemma  (* Remark *) h1 : Rel U A B h.
	Proof.
        apply Rel_intro; do 2 intro; intro h_x_y.
        (* h est sur A *) 
          elim h_x_y.
          (* sur J : f est de A dans B *)
            elim f_inj.
            intro f_Rel; intros.
            elim f_Rel.
            intros f_sur_A f_sur_B.
            apply f_sur_A with y; assumption.

        (* sur A\J: g est de B dans A *)
          elim g_inj.
          intro g_Rel; intros.
          elim g_Rel.
          intros g_sur_B g_sur_A.
          apply g_sur_A with y; assumption.

      (* h est sur B *) 
        elim h_x_y.
        (* sur J : f est de A dans B *)
          elim f_inj.
          intro f_Rel; intros.
          elim f_Rel.
          intros f_sur_A f_sur_B.
          apply f_sur_B with x; assumption.

        (* sur A\J: g est de B dans A *)
        elim g_inj.
        intro g_Rel; intros.
        elim g_Rel.
        intros g_sur_B g_sur_A.
        apply g_sur_B with x; assumption.

    Qed.


    (* h verifie au_plus_une_im *)
    Lemma  (* Remark *) h2 : au_plus_une_im U h.
	Proof.
      red in |- *; intros x y z h_x_y h_x_z.
      elim h_x_y.

      (* sur J *)
        elim h_x_z.
        (* cas ou (h x y) et (h x z) se comporte comme f : correct *)
          elim f_inj.
          unfold au_plus_une_im in |- *; intros f_Rel f_au_plus_1_im; intros.
          apply f_au_plus_1_im with x; assumption.

        (* Cas ou (h x y) se comporte comme f et
                  (h x z) comme g : contradiction *)
          do 2 intro; intro x_in_J; intro.
          cut (Included U J (F J)).
            unfold Included in |- *; unfold F in |- *;
             unfold Setminus in |- *; intro Hyp.
            elim (Hyp x x_in_J).
            intros x_in_A x_in_non_Img.
            elim x_in_non_Img.
            red in |- *.
            red in |- *.
            apply Im_intro with z; assumption.
          exact J_dans_FJ.

      (* sur A\J *)
        elim h_x_z.
        (* Cas ou (h x y) se comporte comme g et
                  (h x z) comme f : contradiction *)
          intro x_in_J; intros.
          cut (Included U J (F J)).
            unfold Included in |- *; unfold F in |- *;
             unfold Setminus in |- *; intro Hyp.
            elim (Hyp x x_in_J).
            intros x_in_A x_in_non_Img.
            elim x_in_non_Img.
            red in |- *.
            red in |- *.
            apply Im_intro with y; assumption.
          exact J_dans_FJ.


        (* cas ou (h x y) et (h x z) se comporte comme g : correct *) 
          elim g_inj.
          unfold au_plus_un_ant in |- *; do 3 intro; intro g_au_plus_1_ant;
           intros.
          apply g_au_plus_1_ant with x; assumption.

    Qed.


    (* h verifie au_moins_une_im *)
    Lemma  (* Remark *) h3 : au_moins_une_im U A h.
	Proof.
      red in |- *.
      intros.
      elim (in_or_not_in U x (Img (Setminus U B (Imf J)))).

      (* sur A\J *)
      unfold Img in |- *; intro x_in_Img.
      elim x_in_Img.
      intros y g_y_x H1.
      exists y.
      apply hr_intro; assumption.

      (* sur J *)
      intros.
        (* De f fonction, on deduit f verifie au_moins_une_im *)
        elim f_inj.
        unfold au_moins_une_im in |- *; do 2 intro; intro f_au_moins_1_im;
         intro.
        elim (f_au_moins_1_im x H).
        intros y f_x_y.
        exists y.
        apply hl_intro.
          apply FJ_dans_J.
          red in |- *; red in |- *; red in |- *.
          split; assumption.
        assumption.

    Qed.


    (* h verifie au_plus_un_ant *)
    Lemma  (* Remark *) h4 : au_plus_un_ant U h.
	Proof.
      red in |- *; do 3 intro; intros h_x_z h_y_z.
      elim h_x_z.

      (* sur J *)
        elim h_y_z.
        (* cas ou (h x y) et (h x z) se comporte comme f : correct *)
          elim f_inj.
          intros.
          cut (forall x y z : U, f x z -> f y z -> x = y).
          intro Hyp; apply Hyp with z; assumption.
          assumption.

        (* Montrer qu'on ne peut avoir (f x z) et (g z y) avec x dans J et
            z hors de (Imf J) sans contradiction *)
          unfold Setminus in |- *; intro z_in_Setminus_B_Imf_J; intros.
          elim z_in_Setminus_B_Imf_J.
          intros z_in_B z_in_non_Imf_J.
          elim z_in_non_Imf_J.
          red in |- *.
          red in |- *.
          apply Im_intro with x; assumption.

      (* sur A\J *)
        elim h_y_z.
        (* Montrer qu'on ne peut avoir (f y z) et (g z x) avec x dans J et
            z hors de (Imf J) sans contradiction *)
          unfold Setminus in |- *; do 2 intro; intro z_in_Setminus_B_Imf_J;
           intros.
          elim z_in_Setminus_B_Imf_J.
          intros z_in_B z_in_non_Imf_J.
          elim z_in_non_Imf_J.
          red in |- *.
          red in |- *.
          apply Im_intro with y; assumption.

        (* De g fonction on deduit g verifie au_plus_une_im c'est-a-dire
                                              au_plus_un_ant pour h *)
          elim g_inj.
          intros.
          cut (forall z x y : U, g z x -> g z y -> x = y).
          intro Hyp; apply Hyp with z; assumption.
          assumption.

    Qed.


    (* h verifie au_moins_un_ant *)
    Lemma  (* Remark *) h5 : au_moins_un_ant U B h.
	Proof.
      red in |- *.
      intros.
      elim (in_or_not_in U y (Imf J)).

      (* sur J *)
      unfold Imf in |- *; intro y_in_Imf.
        (* De f injective on deduit f verifie au_moins_un_ant *)
          elim y_in_Imf.
          intros x f_x_y; intro.
          exists x.
          apply hl_intro; assumption.

      (* sur A\J *)
        intros.
        (* De g injective on deduit g verifie au_moins_une_im c'est-a-dire
                                              au_moins_un_ant pour h *)
          elim g_inj.
          unfold au_moins_une_im in |- *; do 2 intro; intro g_au_moins_1_im;
           intro.
          elim (g_au_moins_1_im y H).
          intros x g_y_x.
          exists x.
          apply hr_intro.
          red in |- *.
          split; assumption.
          assumption.

    Qed.

	Resume h_bij.
    Proof bijection_intro U A B h h1 h2 h3 h4 h5.

  End Bijection.


(*    Le theoreme de Schroeder-Bernstein-Cantor     *)

Theorem Schroeder : inf_card U A B -> inf_card U B A -> equipollence U A B.

  intros A_inf_B B_inf_A.
  elim A_inf_B.
  intros.
  elim B_inf_A.
  intros.
  apply equipollence_intro with (h f f0).
  apply h_bij; assumption.

Qed.


End Schroeder_Bernstein.


                           (* The end *)


(* $Id$ *)