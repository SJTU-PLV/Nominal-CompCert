Require Import Mapsrel.
Require Import Valuesrel.
Require Export Registers.

Module RegmapRel := MapRel(Regmap).

Global Instance regmap_optget_rel:
  Monotonic
    (@regmap_optget)
    (forallr R, - ==> R ++> RegmapRel.r R ++> R).
Proof.
  unfold regmap_optget. rauto.
Qed.

Global Instance regmap_optset_rel:
  Monotonic
    (@regmap_optset)
    (forallr R, - ==> R ++> RegmapRel.r R ++> RegmapRel.r R).
Proof.
  unfold regmap_optset. rauto.
Qed.

Global Instance regmap_setres_rel:
  Monotonic
    (@regmap_setres)
    (forallr R, - ==> R ++> RegmapRel.r R ++> RegmapRel.r R).
Proof.
  unfold regmap_setres. rauto.
Qed.
