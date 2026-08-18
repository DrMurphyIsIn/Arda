/- telperion 0.1.4 | family ShedLemmas | input-hash 6f86e8e48b9c5179
   55 theorems, 55 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace R6
namespace Shed

theorem shed_L1_c0_s16 (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ (132 + 345 * t) / (3680 * (26 + t)) := by
  have hd1 : (26 + t : ℝ) ≠ 0 := by positivity
  have hkey : (132 + 345 * t) / (3680 * (26 + t))
      = (132 + 345 * t)
        / (3680 * (26 + t)) := by
    field_simp
    try ring
  rw [hkey]
  positivity

theorem shed_L1_c0_s14 (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ (41148 + 6831 * t) / (69920 * (26 + t)) := by
  have hd1 : (26 + t : ℝ) ≠ 0 := by positivity
  have hkey : (41148 + 6831 * t) / (69920 * (26 + t))
      = (41148 + 6831 * t)
        / (69920 * (26 + t)) := by
    field_simp
    try ring
  rw [hkey]
  positivity

theorem shed_L1_c1_s16 (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ (66393 + 28548 * t + 1035 * t ^ 2) / (7360 * (26 + t) * (27 + t)) := by
  have hd1 : (26 + t : ℝ) ≠ 0 := by positivity
  have hd2 : (27 + t : ℝ) ≠ 0 := by positivity
  have hkey : (66393 + 28548 * t + 1035 * t ^ 2) / (7360 * (26 + t) * (27 + t))
      = (66393 + 28548 * t + 1035 * t ^ 2)
        / (7360 * (26 + t) * (27 + t)) := by
    field_simp
    try ring
  rw [hkey]
  positivity

theorem shed_L1_c1_s14 (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ (4180167 + 679860 * t + 20493 * t ^ 2) / (139840 * (26 + t) * (27 + t)) := by
  have hd1 : (26 + t : ℝ) ≠ 0 := by positivity
  have hd2 : (27 + t : ℝ) ≠ 0 := by positivity
  have hkey : (4180167 + 679860 * t + 20493 * t ^ 2) / (139840 * (26 + t) * (27 + t))
      = (4180167 + 679860 * t + 20493 * t ^ 2)
        / (139840 * (26 + t) * (27 + t)) := by
    field_simp
    try ring
  rw [hkey]
  positivity

theorem shed_L1_c2_s16 (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ (75222 + 18495 * t + 621 * t ^ 2) / (2944 * (27 + t) * (28 + t)) := by
  have hd1 : (27 + t : ℝ) ≠ 0 := by positivity
  have hd2 : (28 + t : ℝ) ≠ 0 := by positivity
  have hkey : (75222 + 18495 * t + 621 * t ^ 2) / (2944 * (27 + t) * (28 + t))
      = (75222 + 18495 * t + 621 * t ^ 2)
        / (2944 * (27 + t) * (28 + t)) := by
    field_simp
    try ring
  rw [hkey]
  positivity

theorem shed_L1_c2_s14 (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ (15964290 + 2171853 * t + 61479 * t ^ 2) / (279680 * (27 + t) * (28 + t)) := by
  have hd1 : (27 + t : ℝ) ≠ 0 := by positivity
  have hd2 : (28 + t : ℝ) ≠ 0 := by positivity
  have hkey : (15964290 + 2171853 * t + 61479 * t ^ 2) / (279680 * (27 + t) * (28 + t))
      = (15964290 + 2171853 * t + 61479 * t ^ 2)
        / (279680 * (27 + t) * (28 + t)) := by
    field_simp
    try ring
  rw [hkey]
  positivity

theorem shed_L1_c3_s16 (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ (1681479 + 297918 * t + 9315 * t ^ 2) / (29440 * (28 + t) * (29 + t)) := by
  have hd1 : (28 + t : ℝ) ≠ 0 := by positivity
  have hd2 : (29 + t : ℝ) ≠ 0 := by positivity
  have hkey : (1681479 + 297918 * t + 9315 * t ^ 2) / (29440 * (28 + t) * (29 + t))
      = (1681479 + 297918 * t + 9315 * t ^ 2)
        / (29440 * (28 + t) * (29 + t)) := by
    field_simp
    try ring
  rw [hkey]
  positivity

theorem shed_L1_c3_s14 (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ (58589001 + 6912378 * t + 184437 * t ^ 2) / (559360 * (28 + t) * (29 + t)) := by
  have hd1 : (28 + t : ℝ) ≠ 0 := by positivity
  have hd2 : (29 + t : ℝ) ≠ 0 := by positivity
  have hkey : (58589001 + 6912378 * t + 184437 * t ^ 2) / (559360 * (28 + t) * (29 + t))
      = (58589001 + 6912378 * t + 184437 * t ^ 2)
        / (559360 * (28 + t) * (29 + t)) := by
    field_simp
    try ring
  rw [hkey]
  positivity

theorem shed_L1_c4_s16 (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ (6770952 + 955233 * t + 27945 * t ^ 2) / (58880 * (29 + t) * (30 + t)) := by
  have hd1 : (29 + t : ℝ) ≠ 0 := by positivity
  have hd2 : (30 + t : ℝ) ≠ 0 := by positivity
  have hkey : (6770952 + 955233 * t + 27945 * t ^ 2) / (58880 * (29 + t) * (30 + t))
      = (6770952 + 955233 * t + 27945 * t ^ 2)
        / (58880 * (29 + t) * (30 + t)) := by
    field_simp
    try ring
  rw [hkey]
  positivity

theorem shed_L1_c4_s14 (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ (209129688 + 21927591 * t + 553311 * t ^ 2) / (1118720 * (29 + t) * (30 + t)) := by
  have hd1 : (29 + t : ℝ) ≠ 0 := by positivity
  have hd2 : (30 + t : ℝ) ≠ 0 := by positivity
  have hkey : (209129688 + 21927591 * t + 553311 * t ^ 2) / (1118720 * (29 + t) * (30 + t))
      = (209129688 + 21927591 * t + 553311 * t ^ 2)
        / (1118720 * (29 + t) * (30 + t)) := by
    field_simp
    try ring
  rw [hkey]
  positivity

theorem shed_L1_c5_s16 (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ (25693605 + 3050136 * t + 83835 * t ^ 2) / (117760 * (30 + t) * (31 + t)) := by
  have hd1 : (30 + t : ℝ) ≠ 0 := by positivity
  have hd2 : (31 + t : ℝ) ≠ 0 := by positivity
  have hkey : (25693605 + 3050136 * t + 83835 * t ^ 2) / (117760 * (30 + t) * (31 + t))
      = (25693605 + 3050136 * t + 83835 * t ^ 2)
        / (117760 * (30 + t) * (31 + t)) := by
    field_simp
    try ring
  rw [hkey]
  positivity

theorem shed_L1_c5_s14 (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ (731299995 + 69354144 * t + 1659933 * t ^ 2) / (2237440 * (30 + t) * (31 + t)) := by
  have hd1 : (30 + t : ℝ) ≠ 0 := by positivity
  have hd2 : (31 + t : ℝ) ≠ 0 := by positivity
  have hkey : (731299995 + 69354144 * t + 1659933 * t ^ 2) / (2237440 * (30 + t) * (31 + t))
      = (731299995 + 69354144 * t + 1659933 * t ^ 2)
        / (2237440 * (30 + t) * (31 + t)) := by
    field_simp
    try ring
  rw [hkey]
  positivity

theorem shed_L1_c6_s16 (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ (93826674 + 9703719 * t + 251505 * t ^ 2) / (235520 * (31 + t) * (32 + t)) := by
  have hd1 : (31 + t : ℝ) ≠ 0 := by positivity
  have hd2 : (32 + t : ℝ) ≠ 0 := by positivity
  have hkey : (93826674 + 9703719 * t + 251505 * t ^ 2) / (235520 * (31 + t) * (32 + t))
      = (93826674 + 9703719 * t + 251505 * t ^ 2)
        / (235520 * (31 + t) * (32 + t)) := by
    field_simp
    try ring
  rw [hkey]
  positivity

theorem shed_L1_c6_s14 (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ (2517101406 + 218776545 * t + 4979799 * t ^ 2) / (4474880 * (31 + t) * (32 + t)) := by
  have hd1 : (31 + t : ℝ) ≠ 0 := by positivity
  have hd2 : (32 + t : ℝ) ≠ 0 := by positivity
  have hkey : (2517101406 + 218776545 * t + 4979799 * t ^ 2) / (4474880 * (31 + t) * (32 + t))
      = (2517101406 + 218776545 * t + 4979799 * t ^ 2)
        / (4474880 * (31 + t) * (32 + t)) := by
    field_simp
    try ring
  rw [hkey]
  positivity

theorem shed_L1_c7_s16 (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ (66705687 + 6154218 * t + 150903 * t ^ 2) / (94208 * (32 + t) * (33 + t)) := by
  have hd1 : (32 + t : ℝ) ≠ 0 := by positivity
  have hd2 : (33 + t : ℝ) ≠ 0 := by positivity
  have hkey : (66705687 + 6154218 * t + 150903 * t ^ 2) / (94208 * (32 + t) * (33 + t))
      = (66705687 + 6154218 * t + 150903 * t ^ 2)
        / (94208 * (32 + t) * (33 + t)) := by
    field_simp
    try ring
  rw [hkey]
  positivity

theorem shed_L1_c7_s14 (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ (8555314365 + 688471974 * t + 14939397 * t ^ 2) / (8949760 * (32 + t) * (33 + t)) := by
  have hd1 : (32 + t : ℝ) ≠ 0 := by positivity
  have hd2 : (33 + t : ℝ) ≠ 0 := by positivity
  have hkey : (8555314365 + 688471974 * t + 14939397 * t ^ 2) / (8949760 * (32 + t) * (33 + t))
      = (8555314365 + 688471974 * t + 14939397 * t ^ 2)
        / (8949760 * (32 + t) * (33 + t)) := by
    field_simp
    try ring
  rw [hkey]
  positivity

theorem shed_L3_c0_s16 (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ (9685413 + 437805 * t) / (1648640 * (25 + t)) := by
  have hd1 : (25 + t : ℝ) ≠ 0 := by positivity
  have hkey : (9685413 + 437805 * t) / (1648640 * (25 + t))
      = (9685413 + 437805 * t)
        / (1648640 * (25 + t)) := by
    field_simp
    try ring
  rw [hkey]
  positivity

theorem shed_L3_c0_s14 (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ (192778947 + 8668539 * t) / (31324160 * (25 + t)) := by
  have hd1 : (25 + t : ℝ) ≠ 0 := by positivity
  have hkey : (192778947 + 8668539 * t) / (31324160 * (25 + t))
      = (192778947 + 8668539 * t)
        / (31324160 * (25 + t)) := by
    field_simp
    try ring
  rw [hkey]
  positivity

theorem shed_L3_c1_s16 (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ (30632337 + 1313415 * t) / (3297280 * (26 + t)) := by
  have hd1 : (26 + t : ℝ) ≠ 0 := by positivity
  have hkey : (30632337 + 1313415 * t) / (3297280 * (26 + t))
      = (30632337 + 1313415 * t)
        / (3297280 * (26 + t)) := by
    field_simp
    try ring
  rw [hkey]
  positivity

theorem shed_L3_c1_s14 (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ (608282703 + 26005617 * t) / (62648320 * (26 + t)) := by
  have hd1 : (26 + t : ℝ) ≠ 0 := by positivity
  have hkey : (608282703 + 26005617 * t) / (62648320 * (26 + t))
      = (608282703 + 26005617 * t)
        / (62648320 * (26 + t)) := by
    field_simp
    try ring
  rw [hkey]
  positivity

theorem shed_L3_c2_s16 (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ (19325061 + 788049 * t) / (1318912 * (27 + t)) := by
  have hd1 : (27 + t : ℝ) ≠ 0 := by positivity
  have hkey : (19325061 + 788049 * t) / (1318912 * (27 + t))
      = (19325061 + 788049 * t)
        / (1318912 * (27 + t)) := by
    field_simp
    try ring
  rw [hkey]
  positivity

theorem shed_L3_c2_s14 (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ (1914685695 + 78016851 * t) / (125296640 * (27 + t)) := by
  have hd1 : (27 + t : ℝ) ≠ 0 := by positivity
  have hkey : (1914685695 + 78016851 * t) / (125296640 * (27 + t))
      = (1914685695 + 78016851 * t)
        / (125296640 * (27 + t)) := by
    field_simp
    try ring
  rw [hkey]
  positivity

theorem shed_L3_c3_s16 (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ (304060797 + 11820735 * t) / (13189120 * (28 + t)) := by
  have hd1 : (28 + t : ℝ) ≠ 0 := by positivity
  have hkey : (304060797 + 11820735 * t) / (13189120 * (28 + t))
      = (304060797 + 11820735 * t)
        / (13189120 * (28 + t)) := by
    field_simp
    try ring
  rw [hkey]
  positivity

theorem shed_L3_c3_s14 (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ (6013569843 + 234050553 * t) / (250593280 * (28 + t)) := by
  have hd1 : (28 + t : ℝ) ≠ 0 := by positivity
  have hkey : (6013569843 + 234050553 * t) / (250593280 * (28 + t))
      = (6013569843 + 234050553 * t)
        / (250593280 * (28 + t)) := by
    field_simp
    try ring
  rw [hkey]
  positivity

theorem shed_L3_c4_s16 (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ (954737037 + 35462205 * t) / (26378240 * (29 + t)) := by
  have hd1 : (29 + t : ℝ) ≠ 0 := by positivity
  have hkey : (954737037 + 35462205 * t) / (26378240 * (29 + t))
      = (954737037 + 35462205 * t)
        / (26378240 * (29 + t)) := by
    field_simp
    try ring
  rw [hkey]
  positivity

theorem shed_L3_c4_s14 (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ (18849247803 + 702151659 * t) / (501186560 * (29 + t)) := by
  have hd1 : (29 + t : ℝ) ≠ 0 := by positivity
  have hkey : (18849247803 + 702151659 * t) / (501186560 * (29 + t))
      = (18849247803 + 702151659 * t)
        / (501186560 * (29 + t)) := by
    field_simp
    try ring
  rw [hkey]
  positivity

theorem shed_L3_c5_s16 (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ (2991875049 + 106386615 * t) / (52756480 * (30 + t)) := by
  have hd1 : (30 + t : ℝ) ≠ 0 := by positivity
  have hkey : (2991875049 + 106386615 * t) / (52756480 * (30 + t))
      = (2991875049 + 106386615 * t)
        / (52756480 * (30 + t)) := by
    field_simp
    try ring
  rw [hkey]
  positivity

theorem shed_L3_c5_s14 (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ (58973358231 + 2106454977 * t) / (1002373120 * (30 + t)) := by
  have hd1 : (30 + t : ℝ) ≠ 0 := by positivity
  have hkey : (58973358231 + 2106454977 * t) / (1002373120 * (30 + t))
      = (58973358231 + 2106454977 * t)
        / (1002373120 * (30 + t)) := by
    field_simp
    try ring
  rw [hkey]
  positivity

theorem shed_L2_c0_s16 (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ (244764 + 47592 * t + 1035 * t ^ 2) / (10304 * (40 + t) * (41 + t)) := by
  have hd1 : (40 + t : ℝ) ≠ 0 := by positivity
  have hd2 : (41 + t : ℝ) ≠ 0 := by positivity
  have hkey : (244764 + 47592 * t + 1035 * t ^ 2) / (10304 * (40 + t) * (41 + t))
      = (244764 + 47592 * t + 1035 * t ^ 2)
        / (10304 * (40 + t) * (41 + t)) := by
    field_simp
    try ring
  rw [hkey]
  positivity

theorem shed_L2_c0_s14 (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ (11340756 + 1104624 * t + 20493 * t ^ 2) / (195776 * (40 + t) * (41 + t)) := by
  have hd1 : (40 + t : ℝ) ≠ 0 := by positivity
  have hd2 : (41 + t : ℝ) ≠ 0 := by positivity
  have hkey : (11340756 + 1104624 * t + 20493 * t ^ 2) / (195776 * (40 + t) * (41 + t))
      = (11340756 + 1104624 * t + 20493 * t ^ 2)
        / (195776 * (40 + t) * (41 + t)) := by
    field_simp
    try ring
  rw [hkey]
  positivity

theorem shed_L2_c1_s16 (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ (1006236 + 149607 * t + 3105 * t ^ 2) / (20608 * (41 + t) * (42 + t)) := by
  have hd1 : (41 + t : ℝ) ≠ 0 := by positivity
  have hd2 : (42 + t : ℝ) ≠ 0 := by positivity
  have hkey : (1006236 + 149607 * t + 3105 * t ^ 2) / (20608 * (41 + t) * (42 + t))
      = (1006236 + 149607 * t + 3105 * t ^ 2)
        / (20608 * (41 + t) * (42 + t)) := by
    field_simp
    try ring
  rw [hkey]
  positivity

theorem shed_L2_c1_s14 (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ (39288564 + 3446145 * t + 61479 * t ^ 2) / (391552 * (41 + t) * (42 + t)) := by
  have hd1 : (41 + t : ℝ) ≠ 0 := by positivity
  have hd2 : (42 + t : ℝ) ≠ 0 := by positivity
  have hkey : (39288564 + 3446145 * t + 61479 * t ^ 2) / (391552 * (41 + t) * (42 + t))
      = (39288564 + 3446145 * t + 61479 * t ^ 2)
        / (391552 * (41 + t) * (42 + t)) := by
    field_simp
    try ring
  rw [hkey]
  positivity

theorem shed_L2_c2_s16 (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ (3856896 + 469314 * t + 9315 * t ^ 2) / (41216 * (42 + t) * (43 + t)) := by
  have hd1 : (42 + t : ℝ) ≠ 0 := by positivity
  have hd2 : (43 + t : ℝ) ≠ 0 := by positivity
  have hkey : (3856896 + 469314 * t + 9315 * t ^ 2) / (41216 * (42 + t) * (43 + t))
      = (3856896 + 469314 * t + 9315 * t ^ 2)
        / (41216 * (42 + t) * (43 + t)) := by
    field_simp
    try ring
  rw [hkey]
  positivity

theorem shed_L2_c2_s14 (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ (134089344 + 10735254 * t + 184437 * t ^ 2) / (783104 * (42 + t) * (43 + t)) := by
  have hd1 : (42 + t : ℝ) ≠ 0 := by positivity
  have hd2 : (43 + t : ℝ) ≠ 0 := by positivity
  have hkey : (134089344 + 10735254 * t + 184437 * t ^ 2) / (783104 * (42 + t) * (43 + t))
      = (134089344 + 10735254 * t + 184437 * t ^ 2)
        / (783104 * (42 + t) * (43 + t)) := by
    field_simp
    try ring
  rw [hkey]
  positivity

theorem shed_L2_c3_s16 (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ (14152320 + 1469421 * t + 27945 * t ^ 2) / (82432 * (43 + t) * (44 + t)) := by
  have hd1 : (43 + t : ℝ) ≠ 0 := by positivity
  have hd2 : (44 + t : ℝ) ≠ 0 := by positivity
  have hkey : (14152320 + 1469421 * t + 27945 * t ^ 2) / (82432 * (43 + t) * (44 + t))
      = (14152320 + 1469421 * t + 27945 * t ^ 2)
        / (82432 * (43 + t) * (44 + t)) := by
    field_simp
    try ring
  rw [hkey]
  positivity

theorem shed_L2_c3_s14 (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ (452213280 + 33396219 * t + 553311 * t ^ 2) / (1566208 * (43 + t) * (44 + t)) := by
  have hd1 : (43 + t : ℝ) ≠ 0 := by positivity
  have hd2 : (44 + t : ℝ) ≠ 0 := by positivity
  have hkey : (452213280 + 33396219 * t + 553311 * t ^ 2) / (1566208 * (43 + t) * (44 + t))
      = (452213280 + 33396219 * t + 553311 * t ^ 2)
        / (1566208 * (43 + t) * (44 + t)) := by
    field_simp
    try ring
  rw [hkey]
  positivity

theorem shed_L2_c4_s16 (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ (50403060 + 4592700 * t + 83835 * t ^ 2) / (164864 * (44 + t) * (45 + t)) := by
  have hd1 : (44 + t : ℝ) ≠ 0 := by positivity
  have hd2 : (45 + t : ℝ) ≠ 0 := by positivity
  have hkey : (50403060 + 4592700 * t + 83835 * t ^ 2) / (164864 * (44 + t) * (45 + t))
      = (50403060 + 4592700 * t + 83835 * t ^ 2)
        / (164864 * (44 + t) * (45 + t)) := by
    field_simp
    try ring
  rw [hkey]
  positivity

theorem shed_L2_c4_s14 (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ (1510298460 + 103760028 * t + 1659933 * t ^ 2) / (3132416 * (44 + t) * (45 + t)) := by
  have hd1 : (44 + t : ℝ) ≠ 0 := by positivity
  have hd2 : (45 + t : ℝ) ≠ 0 := by positivity
  have hkey : (1510298460 + 103760028 * t + 1659933 * t ^ 2) / (3132416 * (44 + t) * (45 + t))
      = (1510298460 + 103760028 * t + 1659933 * t ^ 2)
        / (3132416 * (44 + t) * (45 + t)) := by
    field_simp
    try ring
  rw [hkey]
  positivity

theorem shed_L2_c5_s16 (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ (175651092 + 14331411 * t + 251505 * t ^ 2) / (329728 * (45 + t) * (46 + t)) := by
  have hd1 : (45 + t : ℝ) ≠ 0 := by positivity
  have hd2 : (46 + t : ℝ) ≠ 0 := by positivity
  have hkey : (175651092 + 14331411 * t + 251505 * t ^ 2) / (329728 * (45 + t) * (46 + t))
      = (175651092 + 14331411 * t + 251505 * t ^ 2)
        / (329728 * (45 + t) * (46 + t)) := by
    field_simp
    try ring
  rw [hkey]
  positivity

theorem shed_L2_c5_s14 (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ (5003339868 + 321994197 * t + 4979799 * t ^ 2) / (6264832 * (45 + t) * (46 + t)) := by
  have hd1 : (45 + t : ℝ) ≠ 0 := by positivity
  have hd2 : (46 + t : ℝ) ≠ 0 := by positivity
  have hkey : (5003339868 + 321994197 * t + 4979799 * t ^ 2) / (6264832 * (45 + t) * (46 + t))
      = (5003339868 + 321994197 * t + 4979799 * t ^ 2)
        / (6264832 * (45 + t) * (46 + t)) := by
    field_simp
    try ring
  rw [hkey]
  positivity

theorem shed_L2_c6_s16 (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ (602089848 + 44654166 * t + 754515 * t ^ 2) / (659456 * (46 + t) * (47 + t)) := by
  have hd1 : (46 + t : ℝ) ≠ 0 := by positivity
  have hd2 : (47 + t : ℝ) ≠ 0 := by positivity
  have hkey : (602089848 + 44654166 * t + 754515 * t ^ 2) / (659456 * (46 + t) * (47 + t))
      = (602089848 + 44654166 * t + 754515 * t ^ 2)
        / (659456 * (46 + t) * (47 + t)) := by
    field_simp
    try ring
  rw [hkey]
  positivity

theorem shed_L2_c6_s14 (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ (16461758952 + 998124930 * t + 14939397 * t ^ 2) / (12529664 * (46 + t) * (47 + t)) := by
  have hd1 : (46 + t : ℝ) ≠ 0 := by positivity
  have hd2 : (47 + t : ℝ) ≠ 0 := by positivity
  have hkey : (16461758952 + 998124930 * t + 14939397 * t ^ 2) / (12529664 * (46 + t) * (47 + t))
      = (16461758952 + 998124930 * t + 14939397 * t ^ 2)
        / (12529664 * (46 + t) * (47 + t)) := by
    field_simp
    try ring
  rw [hkey]
  positivity

theorem shed_L2_c7_s16 (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ (2037111768 + 138942297 * t + 2263545 * t ^ 2) / (1318912 * (47 + t) * (48 + t)) := by
  have hd1 : (47 + t : ℝ) ≠ 0 := by positivity
  have hd2 : (48 + t : ℝ) ≠ 0 := by positivity
  have hkey : (2037111768 + 138942297 * t + 2263545 * t ^ 2) / (1318912 * (47 + t) * (48 + t))
      = (2037111768 + 138942297 * t + 2263545 * t ^ 2)
        / (1318912 * (47 + t) * (48 + t)) := by
    field_simp
    try ring
  rw [hkey]
  positivity

theorem shed_L2_c7_s14 (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ (53843712552 + 3090801807 * t + 44818191 * t ^ 2) / (25059328 * (47 + t) * (48 + t)) := by
  have hd1 : (47 + t : ℝ) ≠ 0 := by positivity
  have hd2 : (48 + t : ℝ) ≠ 0 := by positivity
  have hkey : (53843712552 + 3090801807 * t + 44818191 * t ^ 2) / (25059328 * (47 + t) * (48 + t))
      = (53843712552 + 3090801807 * t + 44818191 * t ^ 2)
        / (25059328 * (47 + t) * (48 + t)) := by
    field_simp
    try ring
  rw [hkey]
  positivity

theorem shed_L4_d0 (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ (1807630958894651651983271659604370 + 97883197931629298722923450148581 * t) / (10115506975539200000000000 * (42 + t)) := by
  have hd1 : (42 + t : ℝ) ≠ 0 := by positivity
  have hkey : (1807630958894651651983271659604370 + 97883197931629298722923450148581 * t) / (10115506975539200000000000 * (42 + t))
      = (1807630958894651651983271659604370 + 97883197931629298722923450148581 * t)
        / (10115506975539200000000000 * (42 + t)) := by
    field_simp
    try ring
  rw [hkey]
  positivity

theorem shed_L4_d1 (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ (2767308751529072793390564857530811160 + 217562791015240954648413742783254024 * t + 3719561521401913351471091105646078 * t ^ 2) / (384389265070489600000000000 * (40 + t) * (42 + t)) := by
  have hd1 : (40 + t : ℝ) ≠ 0 := by positivity
  have hd2 : (42 + t : ℝ) ≠ 0 := by positivity
  have hkey : (2767308751529072793390564857530811160 + 217562791015240954648413742783254024 * t + 3719561521401913351471091105646078 * t ^ 2) / (384389265070489600000000000 * (40 + t) * (42 + t))
      = (2767308751529072793390564857530811160 + 217562791015240954648413742783254024 * t + 3719561521401913351471091105646078 * t ^ 2)
        / (384389265070489600000000000 * (40 + t) * (42 + t)) := by
    field_simp
    try ring
  rw [hkey]
  positivity

theorem shed_L4_d2 (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ (2787018445538275075766556792462979920 + 217653144736408612462619518275698868 * t + 3719561521401913351471091105646078 * t ^ 2) / (384389265070489600000000000 * (40 + t) * (42 + t)) := by
  have hd1 : (40 + t : ℝ) ≠ 0 := by positivity
  have hd2 : (42 + t : ℝ) ≠ 0 := by positivity
  have hkey : (2787018445538275075766556792462979920 + 217653144736408612462619518275698868 * t + 3719561521401913351471091105646078 * t ^ 2) / (384389265070489600000000000 * (40 + t) * (42 + t))
      = (2787018445538275075766556792462979920 + 217653144736408612462619518275698868 * t + 3719561521401913351471091105646078 * t ^ 2)
        / (384389265070489600000000000 * (40 + t) * (42 + t)) := by
    field_simp
    try ring
  rw [hkey]
  positivity

theorem shed_L4_d3 (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ (2806728139547477358142548727395148680 + 217743498457576270276825293768143712 * t + 3719561521401913351471091105646078 * t ^ 2) / (384389265070489600000000000 * (40 + t) * (42 + t)) := by
  have hd1 : (40 + t : ℝ) ≠ 0 := by positivity
  have hd2 : (42 + t : ℝ) ≠ 0 := by positivity
  have hkey : (2806728139547477358142548727395148680 + 217743498457576270276825293768143712 * t + 3719561521401913351471091105646078 * t ^ 2) / (384389265070489600000000000 * (40 + t) * (42 + t))
      = (2806728139547477358142548727395148680 + 217743498457576270276825293768143712 * t + 3719561521401913351471091105646078 * t ^ 2)
        / (384389265070489600000000000 * (40 + t) * (42 + t)) := by
    field_simp
    try ring
  rw [hkey]
  positivity

theorem shed_L4_d4 (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ (2826437833556679640518540662327317440 + 217833852178743928091031069260588556 * t + 3719561521401913351471091105646078 * t ^ 2) / (384389265070489600000000000 * (40 + t) * (42 + t)) := by
  have hd1 : (40 + t : ℝ) ≠ 0 := by positivity
  have hd2 : (42 + t : ℝ) ≠ 0 := by positivity
  have hkey : (2826437833556679640518540662327317440 + 217833852178743928091031069260588556 * t + 3719561521401913351471091105646078 * t ^ 2) / (384389265070489600000000000 * (40 + t) * (42 + t))
      = (2826437833556679640518540662327317440 + 217833852178743928091031069260588556 * t + 3719561521401913351471091105646078 * t ^ 2)
        / (384389265070489600000000000 * (40 + t) * (42 + t)) := by
    field_simp
    try ring
  rw [hkey]
  positivity

theorem shed_L4_d5 (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ (2846147527565881922894532597259486200 + 217924205899911585905236844753033400 * t + 3719561521401913351471091105646078 * t ^ 2) / (384389265070489600000000000 * (40 + t) * (42 + t)) := by
  have hd1 : (40 + t : ℝ) ≠ 0 := by positivity
  have hd2 : (42 + t : ℝ) ≠ 0 := by positivity
  have hkey : (2846147527565881922894532597259486200 + 217924205899911585905236844753033400 * t + 3719561521401913351471091105646078 * t ^ 2) / (384389265070489600000000000 * (40 + t) * (42 + t))
      = (2846147527565881922894532597259486200 + 217924205899911585905236844753033400 * t + 3719561521401913351471091105646078 * t ^ 2)
        / (384389265070489600000000000 * (40 + t) * (42 + t)) := by
    field_simp
    try ring
  rw [hkey]
  positivity

theorem shed_L4_d6 (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ (2865857221575084205270524532191654960 + 218014559621079243719442620245478244 * t + 3719561521401913351471091105646078 * t ^ 2) / (384389265070489600000000000 * (40 + t) * (42 + t)) := by
  have hd1 : (40 + t : ℝ) ≠ 0 := by positivity
  have hd2 : (42 + t : ℝ) ≠ 0 := by positivity
  have hkey : (2865857221575084205270524532191654960 + 218014559621079243719442620245478244 * t + 3719561521401913351471091105646078 * t ^ 2) / (384389265070489600000000000 * (40 + t) * (42 + t))
      = (2865857221575084205270524532191654960 + 218014559621079243719442620245478244 * t + 3719561521401913351471091105646078 * t ^ 2)
        / (384389265070489600000000000 * (40 + t) * (42 + t)) := by
    field_simp
    try ring
  rw [hkey]
  positivity

theorem shed_L4_d7 (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ (2885566915584286487646516467123823720 + 218104913342246901533648395737923088 * t + 3719561521401913351471091105646078 * t ^ 2) / (384389265070489600000000000 * (40 + t) * (42 + t)) := by
  have hd1 : (40 + t : ℝ) ≠ 0 := by positivity
  have hd2 : (42 + t : ℝ) ≠ 0 := by positivity
  have hkey : (2885566915584286487646516467123823720 + 218104913342246901533648395737923088 * t + 3719561521401913351471091105646078 * t ^ 2) / (384389265070489600000000000 * (40 + t) * (42 + t))
      = (2885566915584286487646516467123823720 + 218104913342246901533648395737923088 * t + 3719561521401913351471091105646078 * t ^ 2)
        / (384389265070489600000000000 * (40 + t) * (42 + t)) := by
    field_simp
    try ring
  rw [hkey]
  positivity

theorem shed_L4_d8 (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ (2905276609593488770022508402055992480 + 218195267063414559347854171230367932 * t + 3719561521401913351471091105646078 * t ^ 2) / (384389265070489600000000000 * (40 + t) * (42 + t)) := by
  have hd1 : (40 + t : ℝ) ≠ 0 := by positivity
  have hd2 : (42 + t : ℝ) ≠ 0 := by positivity
  have hkey : (2905276609593488770022508402055992480 + 218195267063414559347854171230367932 * t + 3719561521401913351471091105646078 * t ^ 2) / (384389265070489600000000000 * (40 + t) * (42 + t))
      = (2905276609593488770022508402055992480 + 218195267063414559347854171230367932 * t + 3719561521401913351471091105646078 * t ^ 2)
        / (384389265070489600000000000 * (40 + t) * (42 + t)) := by
    field_simp
    try ring
  rw [hkey]
  positivity

theorem shed_L4_d9 (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ (2924986303602691052398500336988161240 + 218285620784582217162059946722812776 * t + 3719561521401913351471091105646078 * t ^ 2) / (384389265070489600000000000 * (40 + t) * (42 + t)) := by
  have hd1 : (40 + t : ℝ) ≠ 0 := by positivity
  have hd2 : (42 + t : ℝ) ≠ 0 := by positivity
  have hkey : (2924986303602691052398500336988161240 + 218285620784582217162059946722812776 * t + 3719561521401913351471091105646078 * t ^ 2) / (384389265070489600000000000 * (40 + t) * (42 + t))
      = (2924986303602691052398500336988161240 + 218285620784582217162059946722812776 * t + 3719561521401913351471091105646078 * t ^ 2)
        / (384389265070489600000000000 * (40 + t) * (42 + t)) := by
    field_simp
    try ring
  rw [hkey]
  positivity

theorem shed_L4_d10 (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ (2944695997611893334774492271920330000 + 218375974505749874976265722215257620 * t + 3719561521401913351471091105646078 * t ^ 2) / (384389265070489600000000000 * (40 + t) * (42 + t)) := by
  have hd1 : (40 + t : ℝ) ≠ 0 := by positivity
  have hd2 : (42 + t : ℝ) ≠ 0 := by positivity
  have hkey : (2944695997611893334774492271920330000 + 218375974505749874976265722215257620 * t + 3719561521401913351471091105646078 * t ^ 2) / (384389265070489600000000000 * (40 + t) * (42 + t))
      = (2944695997611893334774492271920330000 + 218375974505749874976265722215257620 * t + 3719561521401913351471091105646078 * t ^ 2)
        / (384389265070489600000000000 * (40 + t) * (42 + t)) := by
    field_simp
    try ring
  rw [hkey]
  positivity

end Shed
end R6
