import Mathlib
import PEqualNP.Defs
import PEqualNP.Outside.L_meta_3049
import PEqualNP.Outside.L_meta_7398
import PEqualNP.Outside.L_meta_657

/-!
# Circuit bounds for the 40-vertex graph in L-meta-9840

The target is true when the selected vertices contain the endpoints of one of
the 95 edges in the statement. This file proves the following partial results.

* Every two-input AND/OR/NOT circuit computing the target uses at least 51
  gates. At each of six stages one of the two values of the chosen input
  saves at least two gates. All 64 branches preserve an induced copy of the
  eleven-vertex graph from L-meta-657,
  consisting of three internally disjoint paths of length four with common
  endpoints. Each branch then removes 23 other inputs, saving at least one
  gate per input. The published lower bound on the core is 16. The three
  contributions give 12 + 23 + 16 = 51. The kernel checks every cofactor.
* Every two-input monotone circuit uses at least 59 gates. A perfect matching
  of size 20 supplies the vertex-cover lower bound needed for L-meta-3049.
* An explicit 114-gate monotone circuit computes the target on every input.
  It attains the lower bound in the class defined by GraphClean9840.permit.
  Any monotone circuit with at most 113 gates must have a directed wire path
  from a strict AND accepting at least two edge pairs and a nonedge pair to a
  later AND accepting an edge pair and rejecting every nonedge pair.
* Every monotone formula uses at least 98 leaves. An integer weight matrix
  on 95 positive inputs and 238 negative inputs has weight 975060. Every
  rectangle where a single literal separates the inputs has weight at most
  10029, and 97 × 10029 < 975060. The same leaf bound applies to the formula
  obtained by expanding shared circuit wires separately at each use.
* Adding one point and one nonincident line gives a projective plane of order
  four. The finite checks verify five incidences per point and per line,
  uniqueness of the join of two points and of the meet of two lines, a
  four-point frame, and the exact adjacency table of the punctured plane.

The unrestricted minimum lies between 51 and 114 inclusive. Whether a circuit
of size 113 exists remains open here. The mixed-gate argument adapts the
L-meta-9796 certificate by Simlowker, commit
9392148849ef8174ca73fad6ce913a9dbfdc6410. All finite checks use Lean's kernel.
-/
namespace Simlowker.Graph9840
open PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_7398_aux
def edges : List (Fin 40 × Fin 40) := [(0,20), (0,25), (0,27), (0,37), (1,21), (1,26), (1,28), (1,38), (2,21), (2,22), (2,27), (2,29), (2,39), (3,20), (3,22), (3,23), (3,28), (3,30), (4,23), (4,24), (4,29), (4,31), (5,21), (5,24), (5,25), (5,30), (5,32), (6,22), (6,25), (6,26), (6,31), (6,33), (7,23), (7,26), (7,27), (7,32), (7,34), (8,24), (8,27), (8,28), (8,33), (8,35), (9,25), (9,28), (9,29), (9,34), (9,36), (10,26), (10,29), (10,30), (10,35), (10,37), (11,27), (11,30), (11,31), (11,36), (11,38), (12,28), (12,31), (12,32), (12,37), (12,39), (13,20), (13,29), (13,32), (13,33), (13,38), (14,30), (14,33), (14,34), (14,39), (15,20), (15,21), (15,31), (15,34), (15,35), (16,22), (16,32), (16,35), (16,36), (17,21), (17,23), (17,33), (17,36), (17,37), (18,22), (18,24), (18,34), (18,37), (18,38), (19,23), (19,25), (19,35), (19,38), (19,39)]
def target := fun x : Fin 40 → Bool => (x 0 && x 20) || (x 0 && x 25) || (x 0 && x 27) || (x 0 && x 37) || (x 1 && x 21) || (x 1 && x 26) || (x 1 && x 28) || (x 1 && x 38) || (x 2 && x 21) || (x 2 && x 22) || (x 2 && x 27) || (x 2 && x 29) || (x 2 && x 39) || (x 3 && x 20) || (x 3 && x 22) || (x 3 && x 23) || (x 3 && x 28) || (x 3 && x 30) || (x 4 && x 23) || (x 4 && x 24) || (x 4 && x 29) || (x 4 && x 31) || (x 5 && x 21) || (x 5 && x 24) || (x 5 && x 25) || (x 5 && x 30) || (x 5 && x 32) || (x 6 && x 22) || (x 6 && x 25) || (x 6 && x 26) || (x 6 && x 31) || (x 6 && x 33) || (x 7 && x 23) || (x 7 && x 26) || (x 7 && x 27) || (x 7 && x 32) || (x 7 && x 34) || (x 8 && x 24) || (x 8 && x 27) || (x 8 && x 28) || (x 8 && x 33) || (x 8 && x 35) || (x 9 && x 25) || (x 9 && x 28) || (x 9 && x 29) || (x 9 && x 34) || (x 9 && x 36) || (x 10 && x 26) || (x 10 && x 29) || (x 10 && x 30) || (x 10 && x 35) || (x 10 && x 37) || (x 11 && x 27) || (x 11 && x 30) || (x 11 && x 31) || (x 11 && x 36) || (x 11 && x 38) || (x 12 && x 28) || (x 12 && x 31) || (x 12 && x 32) || (x 12 && x 37) || (x 12 && x 39) || (x 13 && x 20) || (x 13 && x 29) || (x 13 && x 32) || (x 13 && x 33) || (x 13 && x 38) || (x 14 && x 30) || (x 14 && x 33) || (x 14 && x 34) || (x 14 && x 39) || (x 15 && x 20) || (x 15 && x 21) || (x 15 && x 31) || (x 15 && x 34) || (x 15 && x 35) || (x 16 && x 22) || (x 16 && x 32) || (x 16 && x 35) || (x 16 && x 36) || (x 17 && x 21) || (x 17 && x 23) || (x 17 && x 33) || (x 17 && x 36) || (x 17 && x 37) || (x 18 && x 22) || (x 18 && x 24) || (x 18 && x 34) || (x 18 && x 37) || (x 18 && x 38) || (x 19 && x 23) || (x 19 && x 25) || (x 19 && x 35) || (x 19 && x 38) || (x 19 && x 39)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem toGraph : target = gfn [] edges := by
  funext x
  simp only [target, gfn, edges, List.any_cons, List.any_nil, Bool.false_or, Bool.or_false, Bool.or_assoc]
end Simlowker.Graph9840

namespace Simlowker.Graph9840.Anchor
open PEqualNP.Outside.L_meta_7398_aux PEqualNP.MetaComplexity
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def model : List (Fin 11 × Fin 11) := [(0, 2), (2, 3), (3, 4), (4, 1), (0, 5), (5, 6), (6, 7), (7, 1), (0, 8), (8, 9), (9, 10), (10, 1)]
def catalog : List BaseEntry := [⟨11,model,16⟩]
theorem catalogOk : BaseTableOk catalog := by
  apply baseTable_cons
  · intro s h
    apply PEqualNP.Outside.L_meta_657 s
    have eq : gfn [] model = (fun x : Fin 11 → Bool => (x 0 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 1) || (x 0 && x 5) || (x 5 && x 6) || (x 6 && x 7) || (x 7 && x 1) || (x 0 && x 8) || (x 8 && x 9) || (x 9 && x 10) || (x 10 && x 1)) := by
      funext x
      simp only [gfn, model, List.any_cons, List.any_nil, Bool.false_or, Bool.or_false, Bool.or_assoc]
    rwa [←eq]
  · exact fun _ h => by cases h
def t0 : GTree 40 := .base 0 [0,0,0,0,1,0,9,0,3,0,0,0,0,0,0,0,0,6,0,0,0,5,8,7,4,0,0,2,0,0,0,10,0,0,0,0,0,0,0,0]
def t1 : GTree 40 := .f0 39 t0
def t2 : GTree 40 := .f0 19 t1
def t3 : GTree 40 := .f0 38 t2
def t4 : GTree 40 := .f0 37 t3
def t5 : GTree 40 := .f0 36 t4
def t6 : GTree 40 := .f0 35 t5
def t7 : GTree 40 := .f0 14 t6
def t8 : GTree 40 := .f0 34 t7
def t9 : GTree 40 := .f0 33 t8
def t10 : GTree 40 := .f0 16 t9
def t11 : GTree 40 := .f0 32 t10
def t12 : GTree 40 := .f0 30 t11
def t13 : GTree 40 := .f0 29 t12
def t14 : GTree 40 := .f0 25 t13
def t15 : GTree 40 := .f0 18 t14
def t16 : GTree 40 := .f0 15 t15
def t17 : GTree 40 := .f0 13 t16
def t18 : GTree 40 := .f0 12 t17
def t19 : GTree 40 := .f0 11 t18
def t20 : GTree 40 := .f0 10 t19
def t21 : GTree 40 := .f0 9 t20
def t22 : GTree 40 := .f0 7 t21
def t23 : GTree 40 := .f0 5 t22
def t24 : GTree 40 := .base 0 [0,0,0,0,1,6,9,3,0,0,0,0,0,0,0,0,0,0,0,0,0,5,8,4,7,0,0,2,0,0,0,10,0,0,0,0,0,0,0,0]
def t25 : GTree 40 := .f0 39 t24
def t26 : GTree 40 := .f0 19 t25
def t27 : GTree 40 := .f0 38 t26
def t28 : GTree 40 := .f0 17 t27
def t29 : GTree 40 := .f0 37 t28
def t30 : GTree 40 := .f0 36 t29
def t31 : GTree 40 := .f0 35 t30
def t32 : GTree 40 := .f0 34 t31
def t33 : GTree 40 := .f0 33 t32
def t34 : GTree 40 := .f0 32 t33
def t35 : GTree 40 := .f0 30 t34
def t36 : GTree 40 := .f0 29 t35
def t37 : GTree 40 := .f0 25 t36
def t38 : GTree 40 := .f0 18 t37
def t39 : GTree 40 := .f0 16 t38
def t40 : GTree 40 := .f0 15 t39
def t41 : GTree 40 := .f0 14 t40
def t42 : GTree 40 := .f0 13 t41
def t43 : GTree 40 := .f0 11 t42
def t44 : GTree 40 := .f0 10 t43
def t45 : GTree 40 := .f0 12 t44
def t46 : GTree 40 := .f0 9 t45
def t47 : GTree 40 := .f0 8 t46
def t48 : GTree 40 := .b2 28 t23 t47
def t49 : GTree 40 := .base 0 [0,0,0,0,0,1,0,0,3,0,0,0,0,6,0,0,0,0,0,9,0,0,0,0,4,10,0,2,0,5,0,0,7,0,0,0,0,0,0,8]
def t50 : GTree 40 := .f0 37 t49
def t51 : GTree 40 := .f1 17 t50
def t52 : GTree 40 := .f0 38 t51
def t53 : GTree 40 := .f0 36 t52
def t54 : GTree 40 := .f0 35 t53
def t55 : GTree 40 := .f0 15 t54
def t56 : GTree 40 := .f0 34 t55
def t57 : GTree 40 := .f0 33 t56
def t58 : GTree 40 := .f0 31 t57
def t59 : GTree 40 := .f0 21 t58
def t60 : GTree 40 := .f0 18 t59
def t61 : GTree 40 := .f0 16 t60
def t62 : GTree 40 := .f0 14 t61
def t63 : GTree 40 := .f0 12 t62
def t64 : GTree 40 := .f0 11 t63
def t65 : GTree 40 := .f0 10 t64
def t66 : GTree 40 := .f0 9 t65
def t67 : GTree 40 := .f0 7 t66
def t68 : GTree 40 := .f0 6 t67
def t69 : GTree 40 := .f0 30 t68
def t70 : GTree 40 := .f0 28 t69
def t71 : GTree 40 := .f0 23 t70
def t72 : GTree 40 := .f0 22 t71
def t73 : GTree 40 := .base 0 [0,0,0,0,0,0,0,3,0,1,0,0,0,0,0,0,0,6,0,9,0,5,0,0,0,10,0,2,0,0,0,0,0,0,4,0,7,0,0,8]
def t74 : GTree 40 := .f0 38 t73
def t75 : GTree 40 := .f0 37 t74
def t76 : GTree 40 := .f0 35 t75
def t77 : GTree 40 := .f0 33 t76
def t78 : GTree 40 := .f0 32 t77
def t79 : GTree 40 := .f0 18 t78
def t80 : GTree 40 := .f0 16 t79
def t81 : GTree 40 := .f0 15 t80
def t82 : GTree 40 := .f0 14 t81
def t83 : GTree 40 := .f0 13 t82
def t84 : GTree 40 := .f0 12 t83
def t85 : GTree 40 := .f0 11 t84
def t86 : GTree 40 := .f0 10 t85
def t87 : GTree 40 := .f0 8 t86
def t88 : GTree 40 := .f0 6 t87
def t89 : GTree 40 := .f0 5 t88
def t90 : GTree 40 := .f0 31 t89
def t91 : GTree 40 := .f0 30 t90
def t92 : GTree 40 := .f0 29 t91
def t93 : GTree 40 := .f0 28 t92
def t94 : GTree 40 := .f0 24 t93
def t95 : GTree 40 := .f0 23 t94
def t96 : GTree 40 := .f0 22 t95
def t97 : GTree 40 := .b2 4 t72 t96
def t98 : GTree 40 := .b2 3 t48 t97
def t99 : GTree 40 := .base 0 [0,0,0,1,0,6,0,0,0,3,0,0,0,0,0,0,0,0,0,9,0,5,0,10,0,0,0,0,4,2,7,0,0,0,0,0,0,0,0,8]
def t100 : GTree 40 := .f0 38 t99
def t101 : GTree 40 := .f0 17 t100
def t102 : GTree 40 := .f0 37 t101
def t103 : GTree 40 := .f0 36 t102
def t104 : GTree 40 := .f0 35 t103
def t105 : GTree 40 := .f0 34 t104
def t106 : GTree 40 := .f0 33 t105
def t107 : GTree 40 := .f0 32 t106
def t108 : GTree 40 := .f0 15 t107
def t109 : GTree 40 := .f0 31 t108
def t110 : GTree 40 := .f0 24 t109
def t111 : GTree 40 := .f0 22 t110
def t112 : GTree 40 := .f0 18 t111
def t113 : GTree 40 := .f0 16 t112
def t114 : GTree 40 := .f0 14 t113
def t115 : GTree 40 := .f0 13 t114
def t116 : GTree 40 := .f0 12 t115
def t117 : GTree 40 := .f0 11 t116
def t118 : GTree 40 := .f0 8 t117
def t119 : GTree 40 := .f0 4 t118
def t120 : GTree 40 := .f0 10 t119
def t121 : GTree 40 := .f0 7 t120
def t122 : GTree 40 := .f0 6 t121
def t123 : GTree 40 := .base 0 [0,0,0,0,0,1,0,0,0,0,0,0,3,0,0,0,0,9,6,0,0,10,5,8,7,0,0,0,2,0,0,0,4,0,0,0,0,0,0,0]
def t124 : GTree 40 := .f0 39 t123
def t125 : GTree 40 := .f0 38 t124
def t126 : GTree 40 := .f0 37 t125
def t127 : GTree 40 := .f0 36 t126
def t128 : GTree 40 := .f0 19 t127
def t129 : GTree 40 := .f0 35 t128
def t130 : GTree 40 := .f0 34 t129
def t131 : GTree 40 := .f0 33 t130
def t132 : GTree 40 := .f0 31 t131
def t133 : GTree 40 := .f0 30 t132
def t134 : GTree 40 := .f0 13 t133
def t135 : GTree 40 := .f0 29 t134
def t136 : GTree 40 := .f0 16 t135
def t137 : GTree 40 := .f0 15 t136
def t138 : GTree 40 := .f0 14 t137
def t139 : GTree 40 := .f0 9 t138
def t140 : GTree 40 := .f0 4 t139
def t141 : GTree 40 := .f0 11 t140
def t142 : GTree 40 := .f0 10 t141
def t143 : GTree 40 := .f0 8 t142
def t144 : GTree 40 := .f0 7 t143
def t145 : GTree 40 := .f0 6 t144
def t146 : GTree 40 := .f0 2 t145
def t147 : GTree 40 := .b2 27 t122 t146
def t148 : GTree 40 := .base 0 [0,0,0,1,3,0,0,0,6,0,0,0,0,0,9,0,0,0,0,0,0,0,0,4,0,0,0,5,7,2,10,0,0,0,0,0,0,0,0,8]
def t149 : GTree 40 := .f0 38 t148
def t150 : GTree 40 := .f1 18 t149
def t151 : GTree 40 := .f0 36 t150
def t152 : GTree 40 := .f1 16 t151
def t153 : GTree 40 := .f0 37 t152
def t154 : GTree 40 := .f0 35 t153
def t155 : GTree 40 := .f0 34 t154
def t156 : GTree 40 := .f0 33 t155
def t157 : GTree 40 := .f0 32 t156
def t158 : GTree 40 := .f0 31 t157
def t159 : GTree 40 := .f0 24 t158
def t160 : GTree 40 := .f0 22 t159
def t161 : GTree 40 := .f0 17 t160
def t162 : GTree 40 := .f0 15 t161
def t163 : GTree 40 := .f0 13 t162
def t164 : GTree 40 := .f0 12 t163
def t165 : GTree 40 := .f0 11 t164
def t166 : GTree 40 := .f0 19 t165
def t167 : GTree 40 := .f0 10 t166
def t168 : GTree 40 := .f0 9 t167
def t169 : GTree 40 := .f0 7 t168
def t170 : GTree 40 := .f0 6 t169
def t171 : GTree 40 := .f0 5 t170
def t172 : GTree 40 := .base 0 [0,0,0,0,9,0,0,0,1,0,0,0,0,0,3,0,6,0,0,0,0,0,5,8,10,0,0,0,0,0,2,0,0,4,0,7,0,0,0,0]
def t173 : GTree 40 := .f0 39 t172
def t174 : GTree 40 := .f0 18 t173
def t175 : GTree 40 := .f0 38 t174
def t176 : GTree 40 := .f0 37 t175
def t177 : GTree 40 := .f0 36 t176
def t178 : GTree 40 := .f0 34 t177
def t179 : GTree 40 := .f0 32 t178
def t180 : GTree 40 := .f0 31 t179
def t181 : GTree 40 := .f0 29 t180
def t182 : GTree 40 := .f0 28 t181
def t183 : GTree 40 := .f0 27 t182
def t184 : GTree 40 := .f0 13 t183
def t185 : GTree 40 := .f0 12 t184
def t186 : GTree 40 := .f0 11 t185
def t187 : GTree 40 := .f0 19 t186
def t188 : GTree 40 := .f0 17 t187
def t189 : GTree 40 := .f0 15 t188
def t190 : GTree 40 := .f0 10 t189
def t191 : GTree 40 := .f0 9 t190
def t192 : GTree 40 := .f0 7 t191
def t193 : GTree 40 := .f0 6 t192
def t194 : GTree 40 := .f0 5 t193
def t195 : GTree 40 := .f0 2 t194
def t196 : GTree 40 := .b2 21 t171 t195
def t197 : GTree 40 := .b2 25 t147 t196
def t198 : GTree 40 := .b2 26 t98 t197
def t199 : GTree 40 := .base 0 [0,0,0,0,1,0,6,0,3,0,0,0,0,0,0,0,0,0,0,9,0,0,5,10,4,0,0,2,0,0,0,7,0,0,0,0,0,0,0,8]
def t200 : GTree 40 := .f0 18 t199
def t201 : GTree 40 := .f0 37 t200
def t202 : GTree 40 := .f0 16 t201
def t203 : GTree 40 := .f0 36 t202
def t204 : GTree 40 := .f0 35 t203
def t205 : GTree 40 := .f0 34 t204
def t206 : GTree 40 := .f0 33 t205
def t207 : GTree 40 := .f0 32 t206
def t208 : GTree 40 := .f0 14 t207
def t209 : GTree 40 := .f0 30 t208
def t210 : GTree 40 := .f0 29 t209
def t211 : GTree 40 := .f0 25 t210
def t212 : GTree 40 := .f0 17 t211
def t213 : GTree 40 := .f0 12 t212
def t214 : GTree 40 := .f0 11 t213
def t215 : GTree 40 := .f0 10 t214
def t216 : GTree 40 := .f0 9 t215
def t217 : GTree 40 := .f0 7 t216
def t218 : GTree 40 := .f0 5 t217
def t219 : GTree 40 := .f0 38 t218
def t220 : GTree 40 := .f0 28 t219
def t221 : GTree 40 := .f0 26 t220
def t222 : GTree 40 := .f0 21 t221
def t223 : GTree 40 := .base 0 [0,0,0,0,6,1,9,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,8,0,7,10,0,2,0,5,0,0,4,0,0,0,0,0,0,0]
def t224 : GTree 40 := .f0 37 t223
def t225 : GTree 40 := .f1 17 t224
def t226 : GTree 40 := .f0 39 t225
def t227 : GTree 40 := .f0 36 t226
def t228 : GTree 40 := .f0 33 t227
def t229 : GTree 40 := .f0 30 t228
def t230 : GTree 40 := .f0 23 t229
def t231 : GTree 40 := .f0 19 t230
def t232 : GTree 40 := .f0 18 t231
def t233 : GTree 40 := .f0 16 t232
def t234 : GTree 40 := .f0 14 t233
def t235 : GTree 40 := .f0 12 t234
def t236 : GTree 40 := .f0 11 t235
def t237 : GTree 40 := .f0 10 t236
def t238 : GTree 40 := .f0 9 t237
def t239 : GTree 40 := .f0 8 t238
def t240 : GTree 40 := .f0 38 t239
def t241 : GTree 40 := .f0 35 t240
def t242 : GTree 40 := .f0 34 t241
def t243 : GTree 40 := .f0 31 t242
def t244 : GTree 40 := .f0 28 t243
def t245 : GTree 40 := .f0 26 t244
def t246 : GTree 40 := .f0 21 t245
def t247 : GTree 40 := .b2 15 t222 t246
def t248 : GTree 40 := .base 0 [0,0,0,0,0,3,0,6,0,1,0,9,0,0,0,0,0,0,0,0,0,0,0,5,2,4,0,0,0,0,0,8,0,0,7,0,10,0,0,0]
def t249 : GTree 40 := .f0 19 t248
def t250 : GTree 40 := .f0 39 t249
def t251 : GTree 40 := .f0 18 t250
def t252 : GTree 40 := .f0 37 t251
def t253 : GTree 40 := .f0 35 t252
def t254 : GTree 40 := .f0 30 t253
def t255 : GTree 40 := .f0 27 t254
def t256 : GTree 40 := .f0 22 t255
def t257 : GTree 40 := .f0 17 t256
def t258 : GTree 40 := .f0 16 t257
def t259 : GTree 40 := .f0 15 t258
def t260 : GTree 40 := .f0 14 t259
def t261 : GTree 40 := .f0 12 t260
def t262 : GTree 40 := .f0 10 t261
def t263 : GTree 40 := .f0 8 t262
def t264 : GTree 40 := .f0 6 t263
def t265 : GTree 40 := .f0 38 t264
def t266 : GTree 40 := .f0 33 t265
def t267 : GTree 40 := .f0 32 t266
def t268 : GTree 40 := .f0 29 t267
def t269 : GTree 40 := .f0 28 t268
def t270 : GTree 40 := .f0 26 t269
def t271 : GTree 40 := .f0 21 t270
def t272 : GTree 40 := .f0 18 t248
def t273 : GTree 40 := .f0 37 t272
def t274 : GTree 40 := .f0 19 t273
def t275 : GTree 40 := .f0 35 t274
def t276 : GTree 40 := .f0 30 t275
def t277 : GTree 40 := .f0 17 t276
def t278 : GTree 40 := .f0 16 t277
def t279 : GTree 40 := .f0 15 t278
def t280 : GTree 40 := .f0 14 t279
def t281 : GTree 40 := .f0 12 t280
def t282 : GTree 40 := .f0 10 t281
def t283 : GTree 40 := .f0 8 t282
def t284 : GTree 40 := .f0 6 t283
def t285 : GTree 40 := .f0 39 t284
def t286 : GTree 40 := .f0 38 t285
def t287 : GTree 40 := .f0 33 t286
def t288 : GTree 40 := .f0 32 t287
def t289 : GTree 40 := .f0 29 t288
def t290 : GTree 40 := .f0 28 t289
def t291 : GTree 40 := .f0 27 t290
def t292 : GTree 40 := .f0 26 t291
def t293 : GTree 40 := .f0 22 t292
def t294 : GTree 40 := .f0 21 t293
def t295 : GTree 40 := .b2 2 t271 t294
def t296 : GTree 40 := .b2 13 t247 t295
def t297 : GTree 40 := .base 0 [0,0,0,0,0,0,0,0,0,0,1,0,0,3,0,0,0,0,6,9,0,0,0,0,5,8,0,0,0,4,0,0,2,0,0,10,0,7,0,0]
def t298 : GTree 40 := .f0 36 t297
def t299 : GTree 40 := .f1 11 t298
def t300 : GTree 40 := .f0 39 t299
def t301 : GTree 40 := .f0 34 t300
def t302 : GTree 40 := .f0 33 t301
def t303 : GTree 40 := .f0 31 t302
def t304 : GTree 40 := .f0 27 t303
def t305 : GTree 40 := .f0 17 t304
def t306 : GTree 40 := .f0 16 t305
def t307 : GTree 40 := .f0 15 t306
def t308 : GTree 40 := .f0 14 t307
def t309 : GTree 40 := .f0 12 t308
def t310 : GTree 40 := .f0 9 t309
def t311 : GTree 40 := .f0 8 t310
def t312 : GTree 40 := .f0 7 t311
def t313 : GTree 40 := .f0 6 t312
def t314 : GTree 40 := .f0 38 t313
def t315 : GTree 40 := .f0 30 t314
def t316 : GTree 40 := .f0 28 t315
def t317 : GTree 40 := .f0 26 t316
def t318 : GTree 40 := .f0 23 t317
def t319 : GTree 40 := .f0 22 t318
def t320 : GTree 40 := .f0 21 t319
def t321 : GTree 40 := .base 0 [0,0,0,0,0,0,0,0,0,0,0,6,0,3,0,0,0,1,9,0,0,0,0,0,0,0,0,5,0,0,0,0,2,4,8,0,7,10,0,0]
def t322 : GTree 40 := .f0 39 t321
def t323 : GTree 40 := .f1 19 t322
def t324 : GTree 40 := .f0 35 t323
def t325 : GTree 40 := .f0 25 t324
def t326 : GTree 40 := .f0 16 t325
def t327 : GTree 40 := .f0 15 t326
def t328 : GTree 40 := .f0 14 t327
def t329 : GTree 40 := .f0 12 t328
def t330 : GTree 40 := .f0 10 t329
def t331 : GTree 40 := .f0 9 t330
def t332 : GTree 40 := .f0 8 t331
def t333 : GTree 40 := .f0 6 t332
def t334 : GTree 40 := .f0 5 t333
def t335 : GTree 40 := .f0 38 t334
def t336 : GTree 40 := .f0 31 t335
def t337 : GTree 40 := .f0 30 t336
def t338 : GTree 40 := .f0 29 t337
def t339 : GTree 40 := .f0 28 t338
def t340 : GTree 40 := .f0 26 t339
def t341 : GTree 40 := .f0 24 t340
def t342 : GTree 40 := .f0 23 t341
def t343 : GTree 40 := .f0 22 t342
def t344 : GTree 40 := .f0 21 t343
def t345 : GTree 40 := .b2 4 t320 t344
def t346 : GTree 40 := .base 0 [0,0,0,0,0,0,9,3,6,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,5,8,0,0,0,0,0,10,2,0,4,7,0,0,0,0]
def t347 : GTree 40 := .f0 37 t346
def t348 : GTree 40 := .f1 17 t347
def t349 : GTree 40 := .f0 36 t348
def t350 : GTree 40 := .f0 33 t349
def t351 : GTree 40 := .f0 19 t350
def t352 : GTree 40 := .f0 18 t351
def t353 : GTree 40 := .f0 16 t352
def t354 : GTree 40 := .f0 14 t353
def t355 : GTree 40 := .f0 13 t354
def t356 : GTree 40 := .f0 12 t355
def t357 : GTree 40 := .f0 11 t356
def t358 : GTree 40 := .f0 10 t357
def t359 : GTree 40 := .f0 9 t358
def t360 : GTree 40 := .f0 39 t359
def t361 : GTree 40 := .f0 38 t360
def t362 : GTree 40 := .f0 30 t361
def t363 : GTree 40 := .f0 29 t362
def t364 : GTree 40 := .f0 28 t363
def t365 : GTree 40 := .f0 27 t364
def t366 : GTree 40 := .f0 26 t365
def t367 : GTree 40 := .f0 23 t366
def t368 : GTree 40 := .f0 22 t367
def t369 : GTree 40 := .f0 21 t368
def t370 : GTree 40 := .base 0 [0,0,0,0,0,0,8,4,0,2,0,0,0,10,0,0,7,0,0,5,0,0,0,0,0,0,0,0,0,0,0,0,1,9,3,6,0,0,0,0]
def t371 : GTree 40 := .f0 18 t370
def t372 : GTree 40 := .f0 37 t371
def t373 : GTree 40 := .f0 36 t372
def t374 : GTree 40 := .f0 17 t373
def t375 : GTree 40 := .f0 15 t374
def t376 : GTree 40 := .f0 14 t375
def t377 : GTree 40 := .f0 12 t376
def t378 : GTree 40 := .f0 11 t377
def t379 : GTree 40 := .f0 10 t378
def t380 : GTree 40 := .f0 8 t379
def t381 : GTree 40 := .f0 5 t380
def t382 : GTree 40 := .f0 39 t381
def t383 : GTree 40 := .f0 38 t382
def t384 : GTree 40 := .f0 31 t383
def t385 : GTree 40 := .f0 30 t384
def t386 : GTree 40 := .f0 29 t385
def t387 : GTree 40 := .f0 28 t386
def t388 : GTree 40 := .f0 27 t387
def t389 : GTree 40 := .f0 26 t388
def t390 : GTree 40 := .f0 24 t389
def t391 : GTree 40 := .f0 23 t390
def t392 : GTree 40 := .f0 22 t391
def t393 : GTree 40 := .f0 21 t392
def t394 : GTree 40 := .b2 4 t369 t393
def t395 : GTree 40 := .b2 2 t345 t394
def t396 : GTree 40 := .b2 3 t296 t395
def t397 : GTree 40 := .b2 1 t198 t396
def t398 : GTree 40 := .f0 38 t199
def t399 : GTree 40 := .f0 18 t398
def t400 : GTree 40 := .f0 37 t399
def t401 : GTree 40 := .f0 16 t400
def t402 : GTree 40 := .f0 36 t401
def t403 : GTree 40 := .f0 35 t402
def t404 : GTree 40 := .f0 34 t403
def t405 : GTree 40 := .f0 33 t404
def t406 : GTree 40 := .f0 32 t405
def t407 : GTree 40 := .f0 14 t406
def t408 : GTree 40 := .f0 30 t407
def t409 : GTree 40 := .f0 29 t408
def t410 : GTree 40 := .f0 25 t409
def t411 : GTree 40 := .f0 17 t410
def t412 : GTree 40 := .f0 12 t411
def t413 : GTree 40 := .f0 11 t412
def t414 : GTree 40 := .f0 10 t413
def t415 : GTree 40 := .f0 9 t414
def t416 : GTree 40 := .f0 7 t415
def t417 : GTree 40 := .f0 5 t416
def t418 : GTree 40 := .f0 15 t417
def t419 : GTree 40 := .f0 13 t418
def t420 : GTree 40 := .f0 3 t419
def t421 : GTree 40 := .base 0 [0,0,0,0,1,0,0,0,0,0,0,3,0,0,0,0,0,0,6,9,0,0,5,10,7,0,0,2,0,0,0,4,0,0,0,0,0,0,0,8]
def t422 : GTree 40 := .f0 38 t421
def t423 : GTree 40 := .f0 37 t422
def t424 : GTree 40 := .f0 36 t423
def t425 : GTree 40 := .f0 35 t424
def t426 : GTree 40 := .f0 34 t425
def t427 : GTree 40 := .f0 17 t426
def t428 : GTree 40 := .f0 33 t427
def t429 : GTree 40 := .f0 16 t428
def t430 : GTree 40 := .f0 32 t429
def t431 : GTree 40 := .f0 30 t430
def t432 : GTree 40 := .f0 29 t431
def t433 : GTree 40 := .f0 25 t432
def t434 : GTree 40 := .f0 14 t433
def t435 : GTree 40 := .f0 10 t434
def t436 : GTree 40 := .f0 7 t435
def t437 : GTree 40 := .f0 6 t436
def t438 : GTree 40 := .f0 5 t437
def t439 : GTree 40 := .f0 15 t438
def t440 : GTree 40 := .f0 13 t439
def t441 : GTree 40 := .f0 12 t440
def t442 : GTree 40 := .f0 9 t441
def t443 : GTree 40 := .f0 8 t442
def t444 : GTree 40 := .f0 3 t443
def t445 : GTree 40 := .b2 28 t420 t444
def t446 : GTree 40 := .base 0 [0,0,0,0,0,1,0,0,3,6,0,0,9,0,0,0,0,0,0,0,0,0,0,0,4,7,0,2,0,5,0,0,10,0,0,0,0,0,0,8]
def t447 : GTree 40 := .f0 19 t446
def t448 : GTree 40 := .f0 38 t447
def t449 : GTree 40 := .f0 37 t448
def t450 : GTree 40 := .f0 36 t449
def t451 : GTree 40 := .f0 35 t450
def t452 : GTree 40 := .f0 34 t451
def t453 : GTree 40 := .f0 33 t452
def t454 : GTree 40 := .f0 31 t453
def t455 : GTree 40 := .f0 30 t454
def t456 : GTree 40 := .f0 28 t455
def t457 : GTree 40 := .f0 23 t456
def t458 : GTree 40 := .f0 18 t457
def t459 : GTree 40 := .f0 17 t458
def t460 : GTree 40 := .f0 16 t459
def t461 : GTree 40 := .f0 14 t460
def t462 : GTree 40 := .f0 11 t461
def t463 : GTree 40 := .f0 4 t462
def t464 : GTree 40 := .f0 15 t463
def t465 : GTree 40 := .f0 13 t464
def t466 : GTree 40 := .f0 10 t465
def t467 : GTree 40 := .f0 7 t466
def t468 : GTree 40 := .f0 6 t467
def t469 : GTree 40 := .f0 3 t468
def t470 : GTree 40 := .base 0 [0,0,0,0,0,0,0,0,1,6,0,9,0,0,0,0,0,3,0,0,0,0,0,2,0,0,0,10,7,5,0,8,0,4,0,0,0,0,0,0]
def t471 : GTree 40 := .f0 12 t470
def t472 : GTree 40 := .f0 39 t471
def t473 : GTree 40 := .f0 38 t472
def t474 : GTree 40 := .f0 37 t473
def t475 : GTree 40 := .f0 36 t474
def t476 : GTree 40 := .f0 35 t475
def t477 : GTree 40 := .f0 34 t476
def t478 : GTree 40 := .f0 32 t477
def t479 : GTree 40 := .f0 30 t478
def t480 : GTree 40 := .f0 25 t479
def t481 : GTree 40 := .f0 24 t480
def t482 : GTree 40 := .f0 19 t481
def t483 : GTree 40 := .f0 14 t482
def t484 : GTree 40 := .f0 5 t483
def t485 : GTree 40 := .f0 18 t484
def t486 : GTree 40 := .f0 16 t485
def t487 : GTree 40 := .f0 15 t486
def t488 : GTree 40 := .f0 13 t487
def t489 : GTree 40 := .f0 10 t488
def t490 : GTree 40 := .f0 7 t489
def t491 : GTree 40 := .f0 6 t490
def t492 : GTree 40 := .f0 3 t491
def t493 : GTree 40 := .f0 2 t492
def t494 : GTree 40 := .b2 22 t469 t493
def t495 : GTree 40 := .b2 26 t445 t494
def t496 : GTree 40 := .base 0 [0,0,0,0,0,0,1,0,3,0,6,0,0,0,0,0,0,0,0,9,0,0,0,8,2,10,7,0,0,5,0,0,0,4,0,0,0,0,0,0]
def t497 : GTree 40 := .f0 39 t496
def t498 : GTree 40 := .f0 38 t497
def t499 : GTree 40 := .f0 37 t498
def t500 : GTree 40 := .f0 11 t499
def t501 : GTree 40 := .f0 36 t500
def t502 : GTree 40 := .f0 35 t501
def t503 : GTree 40 := .f0 18 t502
def t504 : GTree 40 := .f0 34 t503
def t505 : GTree 40 := .f0 12 t504
def t506 : GTree 40 := .f0 32 t505
def t507 : GTree 40 := .f0 31 t506
def t508 : GTree 40 := .f0 30 t507
def t509 : GTree 40 := .f0 28 t508
def t510 : GTree 40 := .f0 27 t509
def t511 : GTree 40 := .f0 14 t510
def t512 : GTree 40 := .f0 9 t511
def t513 : GTree 40 := .f0 7 t512
def t514 : GTree 40 := .f0 17 t513
def t515 : GTree 40 := .f0 15 t514
def t516 : GTree 40 := .f0 13 t515
def t517 : GTree 40 := .f0 5 t516
def t518 : GTree 40 := .f0 3 t517
def t519 : GTree 40 := .f0 2 t518
def t520 : GTree 40 := .f0 18 t499
def t521 : GTree 40 := .f0 34 t520
def t522 : GTree 40 := .f0 31 t521
def t523 : GTree 40 := .f0 30 t522
def t524 : GTree 40 := .f0 28 t523
def t525 : GTree 40 := .f0 27 t524
def t526 : GTree 40 := .f0 14 t525
def t527 : GTree 40 := .f0 12 t526
def t528 : GTree 40 := .f0 11 t527
def t529 : GTree 40 := .f0 9 t528
def t530 : GTree 40 := .f0 7 t529
def t531 : GTree 40 := .f0 36 t530
def t532 : GTree 40 := .f0 35 t531
def t533 : GTree 40 := .f0 32 t532
def t534 : GTree 40 := .f0 17 t533
def t535 : GTree 40 := .f0 15 t534
def t536 : GTree 40 := .f0 13 t535
def t537 : GTree 40 := .f0 5 t536
def t538 : GTree 40 := .f0 3 t537
def t539 : GTree 40 := .f0 2 t538
def t540 : GTree 40 := .b2 16 t519 t539
def t541 : GTree 40 := .base 0 [0,0,0,0,0,0,0,3,1,0,6,0,9,0,0,0,0,0,0,0,0,0,0,2,0,0,0,4,10,5,0,8,0,0,0,7,0,0,0,0]
def t542 : GTree 40 := .f0 39 t541
def t543 : GTree 40 := .f0 11 t542
def t544 : GTree 40 := .f0 38 t543
def t545 : GTree 40 := .f0 37 t544
def t546 : GTree 40 := .f0 36 t545
def t547 : GTree 40 := .f0 34 t546
def t548 : GTree 40 := .f0 33 t547
def t549 : GTree 40 := .f0 32 t548
def t550 : GTree 40 := .f0 30 t549
def t551 : GTree 40 := .f0 26 t550
def t552 : GTree 40 := .f0 19 t551
def t553 : GTree 40 := .f0 25 t552
def t554 : GTree 40 := .f0 14 t553
def t555 : GTree 40 := .f0 9 t554
def t556 : GTree 40 := .f0 18 t555
def t557 : GTree 40 := .f0 17 t556
def t558 : GTree 40 := .f0 16 t557
def t559 : GTree 40 := .f0 15 t558
def t560 : GTree 40 := .f0 13 t559
def t561 : GTree 40 := .f0 6 t560
def t562 : GTree 40 := .f0 5 t561
def t563 : GTree 40 := .f0 3 t562
def t564 : GTree 40 := .f0 2 t563
def t565 : GTree 40 := .base 0 [0,0,0,0,0,0,0,0,0,1,6,9,3,0,0,0,0,0,0,0,0,0,0,0,0,0,5,8,4,7,0,0,2,0,0,0,10,0,0,0]
def t566 : GTree 40 := .f0 39 t565
def t567 : GTree 40 := .f0 38 t566
def t568 : GTree 40 := .f0 37 t567
def t569 : GTree 40 := .f0 35 t568
def t570 : GTree 40 := .f0 34 t569
def t571 : GTree 40 := .f0 14 t570
def t572 : GTree 40 := .f0 33 t571
def t573 : GTree 40 := .f0 31 t572
def t574 : GTree 40 := .f0 30 t573
def t575 : GTree 40 := .f0 25 t574
def t576 : GTree 40 := .f0 23 t575
def t577 : GTree 40 := .f0 19 t576
def t578 : GTree 40 := .f0 18 t577
def t579 : GTree 40 := .f0 17 t578
def t580 : GTree 40 := .f0 16 t579
def t581 : GTree 40 := .f0 15 t580
def t582 : GTree 40 := .f0 13 t581
def t583 : GTree 40 := .f0 8 t582
def t584 : GTree 40 := .f0 6 t583
def t585 : GTree 40 := .f0 5 t584
def t586 : GTree 40 := .f0 4 t585
def t587 : GTree 40 := .f0 3 t586
def t588 : GTree 40 := .f0 2 t587
def t589 : GTree 40 := .b2 24 t564 t588
def t590 : GTree 40 := .b2 22 t540 t589
def t591 : GTree 40 := .b2 21 t495 t590
def t592 : GTree 40 := .base 0 [0,0,0,0,0,1,0,3,0,6,0,9,0,0,0,0,0,0,0,0,0,0,0,2,0,7,0,0,0,5,10,8,4,0,0,0,0,0,0,0]
def t593 : GTree 40 := .f0 19 t592
def t594 : GTree 40 := .f0 39 t593
def t595 : GTree 40 := .f0 17 t594
def t596 : GTree 40 := .f0 37 t595
def t597 : GTree 40 := .f0 36 t596
def t598 : GTree 40 := .f0 35 t597
def t599 : GTree 40 := .f0 34 t598
def t600 : GTree 40 := .f0 33 t599
def t601 : GTree 40 := .f0 27 t600
def t602 : GTree 40 := .f0 24 t601
def t603 : GTree 40 := .f0 18 t602
def t604 : GTree 40 := .f0 16 t603
def t605 : GTree 40 := .f0 14 t604
def t606 : GTree 40 := .f0 12 t605
def t607 : GTree 40 := .f0 10 t606
def t608 : GTree 40 := .f0 8 t607
def t609 : GTree 40 := .f0 38 t608
def t610 : GTree 40 := .f0 28 t609
def t611 : GTree 40 := .f0 26 t610
def t612 : GTree 40 := .f0 21 t611
def t613 : GTree 40 := .f0 15 t612
def t614 : GTree 40 := .f0 13 t613
def t615 : GTree 40 := .f0 3 t614
def t616 : GTree 40 := .base 0 [0,0,0,0,0,0,0,0,3,0,6,1,0,0,0,0,0,9,0,0,0,0,0,8,2,0,0,4,0,5,7,0,0,0,0,0,10,0,0,0]
def t617 : GTree 40 := .f0 19 t616
def t618 : GTree 40 := .f0 39 t617
def t619 : GTree 40 := .f0 37 t618
def t620 : GTree 40 := .f0 35 t619
def t621 : GTree 40 := .f0 18 t620
def t622 : GTree 40 := .f0 34 t621
def t623 : GTree 40 := .f0 16 t622
def t624 : GTree 40 := .f0 32 t623
def t625 : GTree 40 := .f0 14 t624
def t626 : GTree 40 := .f0 12 t625
def t627 : GTree 40 := .f0 9 t626
def t628 : GTree 40 := .f0 7 t627
def t629 : GTree 40 := .f0 5 t628
def t630 : GTree 40 := .f0 38 t629
def t631 : GTree 40 := .f0 33 t630
def t632 : GTree 40 := .f0 31 t631
def t633 : GTree 40 := .f0 28 t632
def t634 : GTree 40 := .f0 26 t633
def t635 : GTree 40 := .f0 25 t634
def t636 : GTree 40 := .f0 21 t635
def t637 : GTree 40 := .f0 15 t636
def t638 : GTree 40 := .f0 13 t637
def t639 : GTree 40 := .f0 3 t638
def t640 : GTree 40 := .b2 6 t615 t639
def t641 : GTree 40 := .f0 14 t601
def t642 : GTree 40 := .f0 12 t641
def t643 : GTree 40 := .f0 10 t642
def t644 : GTree 40 := .f0 8 t643
def t645 : GTree 40 := .f0 38 t644
def t646 : GTree 40 := .f0 28 t645
def t647 : GTree 40 := .f0 26 t646
def t648 : GTree 40 := .f0 21 t647
def t649 : GTree 40 := .f0 18 t648
def t650 : GTree 40 := .f0 16 t649
def t651 : GTree 40 := .f0 15 t650
def t652 : GTree 40 := .f0 13 t651
def t653 : GTree 40 := .f0 6 t652
def t654 : GTree 40 := .f0 3 t653
def t655 : GTree 40 := .base 0 [0,0,0,0,0,0,0,0,0,6,1,9,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,8,0,7,10,0,2,0,5,0,0,4,0,0]
def t656 : GTree 40 := .f0 39 t655
def t657 : GTree 40 := .f0 36 t656
def t658 : GTree 40 := .f0 35 t657
def t659 : GTree 40 := .f0 17 t658
def t660 : GTree 40 := .f0 33 t659
def t661 : GTree 40 := .f0 31 t660
def t662 : GTree 40 := .f0 25 t661
def t663 : GTree 40 := .f0 23 t662
def t664 : GTree 40 := .f0 19 t663
def t665 : GTree 40 := .f0 14 t664
def t666 : GTree 40 := .f0 38 t665
def t667 : GTree 40 := .f0 28 t666
def t668 : GTree 40 := .f0 26 t667
def t669 : GTree 40 := .f0 21 t668
def t670 : GTree 40 := .f0 18 t669
def t671 : GTree 40 := .f0 16 t670
def t672 : GTree 40 := .f0 15 t671
def t673 : GTree 40 := .f0 13 t672
def t674 : GTree 40 := .f0 8 t673
def t675 : GTree 40 := .f0 6 t674
def t676 : GTree 40 := .f0 5 t675
def t677 : GTree 40 := .f0 4 t676
def t678 : GTree 40 := .f0 3 t677
def t679 : GTree 40 := .b2 24 t654 t678
def t680 : GTree 40 := .b2 22 t640 t679
def t681 : GTree 40 := .base 0 [0,0,0,0,0,0,0,0,6,0,0,0,0,0,0,0,3,1,0,9,0,0,0,10,5,8,0,0,0,0,0,0,2,7,0,0,4,0,0,0]
def t682 : GTree 40 := .f0 37 t681
def t683 : GTree 40 := .f0 35 t682
def t684 : GTree 40 := .f0 18 t683
def t685 : GTree 40 := .f0 34 t684
def t686 : GTree 40 := .f0 12 t685
def t687 : GTree 40 := .f0 31 t686
def t688 : GTree 40 := .f0 30 t687
def t689 : GTree 40 := .f0 14 t688
def t690 : GTree 40 := .f0 11 t689
def t691 : GTree 40 := .f0 10 t690
def t692 : GTree 40 := .f0 9 t691
def t693 : GTree 40 := .f0 7 t692
def t694 : GTree 40 := .f0 39 t693
def t695 : GTree 40 := .f0 38 t694
def t696 : GTree 40 := .f0 29 t695
def t697 : GTree 40 := .f0 28 t696
def t698 : GTree 40 := .f0 27 t697
def t699 : GTree 40 := .f0 26 t698
def t700 : GTree 40 := .f0 22 t699
def t701 : GTree 40 := .f0 21 t700
def t702 : GTree 40 := .f0 15 t701
def t703 : GTree 40 := .f0 13 t702
def t704 : GTree 40 := .f0 3 t703
def t705 : GTree 40 := .base 0 [0,0,0,0,0,0,0,3,0,0,0,9,0,0,0,0,0,1,6,0,0,0,0,4,5,0,0,0,0,0,8,0,2,0,0,0,10,7,0,0]
def t706 : GTree 40 := .f0 19 t705
def t707 : GTree 40 := .f0 35 t706
def t708 : GTree 40 := .f0 34 t707
def t709 : GTree 40 := .f0 16 t708
def t710 : GTree 40 := .f0 14 t709
def t711 : GTree 40 := .f0 12 t710
def t712 : GTree 40 := .f0 10 t711
def t713 : GTree 40 := .f0 9 t712
def t714 : GTree 40 := .f0 8 t713
def t715 : GTree 40 := .f0 39 t714
def t716 : GTree 40 := .f0 38 t715
def t717 : GTree 40 := .f0 33 t716
def t718 : GTree 40 := .f0 31 t717
def t719 : GTree 40 := .f0 29 t718
def t720 : GTree 40 := .f0 28 t719
def t721 : GTree 40 := .f0 27 t720
def t722 : GTree 40 := .f0 26 t721
def t723 : GTree 40 := .f0 25 t722
def t724 : GTree 40 := .f0 22 t723
def t725 : GTree 40 := .f0 21 t724
def t726 : GTree 40 := .f0 15 t725
def t727 : GTree 40 := .f0 13 t726
def t728 : GTree 40 := .f0 3 t727
def t729 : GTree 40 := .b2 6 t704 t728
def t730 : GTree 40 := .base 0 [0,0,0,0,0,0,0,0,0,6,0,0,3,0,9,0,0,1,0,0,0,0,0,0,0,5,0,0,0,0,8,0,2,10,0,0,7,4,0,0]
def t731 : GTree 40 := .f0 19 t730
def t732 : GTree 40 := .f0 35 t731
def t733 : GTree 40 := .f0 34 t732
def t734 : GTree 40 := .f0 18 t733
def t735 : GTree 40 := .f0 16 t734
def t736 : GTree 40 := .f0 11 t735
def t737 : GTree 40 := .f0 10 t736
def t738 : GTree 40 := .f0 8 t737
def t739 : GTree 40 := .f0 7 t738
def t740 : GTree 40 := .f0 39 t739
def t741 : GTree 40 := .f0 38 t740
def t742 : GTree 40 := .f0 31 t741
def t743 : GTree 40 := .f0 29 t742
def t744 : GTree 40 := .f0 28 t743
def t745 : GTree 40 := .f0 27 t744
def t746 : GTree 40 := .f0 26 t745
def t747 : GTree 40 := .f0 24 t746
def t748 : GTree 40 := .f0 23 t747
def t749 : GTree 40 := .f0 22 t748
def t750 : GTree 40 := .f0 21 t749
def t751 : GTree 40 := .f0 15 t750
def t752 : GTree 40 := .f0 13 t751
def t753 : GTree 40 := .f0 3 t752
def t754 : GTree 40 := .base 0 [0,0,0,0,0,0,0,10,0,0,5,2,7,0,8,0,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,9,0,3,6,0,0]
def t755 : GTree 40 := .f0 35 t754
def t756 : GTree 40 := .f0 19 t755
def t757 : GTree 40 := .f0 18 t756
def t758 : GTree 40 := .f0 17 t757
def t759 : GTree 40 := .f0 9 t758
def t760 : GTree 40 := .f0 8 t759
def t761 : GTree 40 := .f0 5 t760
def t762 : GTree 40 := .f0 39 t761
def t763 : GTree 40 := .f0 38 t762
def t764 : GTree 40 := .f0 33 t763
def t765 : GTree 40 := .f0 31 t764
def t766 : GTree 40 := .f0 29 t765
def t767 : GTree 40 := .f0 28 t766
def t768 : GTree 40 := .f0 27 t767
def t769 : GTree 40 := .f0 26 t768
def t770 : GTree 40 := .f0 25 t769
def t771 : GTree 40 := .f0 24 t770
def t772 : GTree 40 := .f0 23 t771
def t773 : GTree 40 := .f0 22 t772
def t774 : GTree 40 := .f0 21 t773
def t775 : GTree 40 := .f0 15 t774
def t776 : GTree 40 := .f0 13 t775
def t777 : GTree 40 := .f0 3 t776
def t778 : GTree 40 := .b2 6 t753 t777
def t779 : GTree 40 := .b2 4 t729 t778
def t780 : GTree 40 := .b2 2 t680 t779
def t781 : GTree 40 := .b2 1 t591 t780
def t782 : GTree 40 := .b2 20 t397 t781
def t783 : GTree 40 := .f0 36 t100
def t784 : GTree 40 := .f0 35 t783
def t785 : GTree 40 := .f0 34 t784
def t786 : GTree 40 := .f0 17 t785
def t787 : GTree 40 := .f0 33 t786
def t788 : GTree 40 := .f0 32 t787
def t789 : GTree 40 := .f0 15 t788
def t790 : GTree 40 := .f0 31 t789
def t791 : GTree 40 := .f0 24 t790
def t792 : GTree 40 := .f0 22 t791
def t793 : GTree 40 := .f0 18 t792
def t794 : GTree 40 := .f0 16 t793
def t795 : GTree 40 := .f0 14 t794
def t796 : GTree 40 := .f0 13 t795
def t797 : GTree 40 := .f0 12 t796
def t798 : GTree 40 := .f0 11 t797
def t799 : GTree 40 := .f0 8 t798
def t800 : GTree 40 := .f0 4 t799
def t801 : GTree 40 := .f0 37 t800
def t802 : GTree 40 := .f0 27 t801
def t803 : GTree 40 := .f0 25 t802
def t804 : GTree 40 := .f0 20 t803
def t805 : GTree 40 := .base 0 [0,0,0,6,1,3,0,0,0,0,0,0,9,0,0,0,0,0,0,0,0,2,5,7,4,0,0,0,0,0,0,10,0,0,0,0,0,0,0,8]
def t806 : GTree 40 := .f0 18 t805
def t807 : GTree 40 := .f0 38 t806
def t808 : GTree 40 := .f0 17 t807
def t809 : GTree 40 := .f0 36 t808
def t810 : GTree 40 := .f0 34 t809
def t811 : GTree 40 := .f0 33 t810
def t812 : GTree 40 := .f0 32 t811
def t813 : GTree 40 := .f0 28 t812
def t814 : GTree 40 := .f0 19 t813
def t815 : GTree 40 := .f0 16 t814
def t816 : GTree 40 := .f0 15 t815
def t817 : GTree 40 := .f0 14 t816
def t818 : GTree 40 := .f0 13 t817
def t819 : GTree 40 := .f0 11 t818
def t820 : GTree 40 := .f0 9 t819
def t821 : GTree 40 := .f0 8 t820
def t822 : GTree 40 := .f0 37 t821
def t823 : GTree 40 := .f0 35 t822
def t824 : GTree 40 := .f0 30 t823
def t825 : GTree 40 := .f0 29 t824
def t826 : GTree 40 := .f0 27 t825
def t827 : GTree 40 := .f0 25 t826
def t828 : GTree 40 := .f0 20 t827
def t829 : GTree 40 := .b2 10 t804 t828
def t830 : GTree 40 := .base 0 [0,0,0,0,3,0,0,0,1,0,0,0,0,0,0,0,9,6,0,0,0,5,8,0,4,0,0,0,0,2,0,0,0,7,0,10,0,0,0,0]
def t831 : GTree 40 := .f0 39 t830
def t832 : GTree 40 := .f0 19 t831
def t833 : GTree 40 := .f0 38 t832
def t834 : GTree 40 := .f0 36 t833
def t835 : GTree 40 := .f0 31 t834
def t836 : GTree 40 := .f0 14 t835
def t837 : GTree 40 := .f0 30 t836
def t838 : GTree 40 := .f0 28 t837
def t839 : GTree 40 := .f0 18 t838
def t840 : GTree 40 := .f0 15 t839
def t841 : GTree 40 := .f0 13 t840
def t842 : GTree 40 := .f0 12 t841
def t843 : GTree 40 := .f0 11 t842
def t844 : GTree 40 := .f0 10 t843
def t845 : GTree 40 := .f0 9 t844
def t846 : GTree 40 := .f0 5 t845
def t847 : GTree 40 := .f0 37 t846
def t848 : GTree 40 := .f0 34 t847
def t849 : GTree 40 := .f0 32 t848
def t850 : GTree 40 := .f0 27 t849
def t851 : GTree 40 := .f0 25 t850
def t852 : GTree 40 := .f0 23 t851
def t853 : GTree 40 := .f0 20 t852
def t854 : GTree 40 := .base 0 [0,0,0,0,3,0,0,0,1,0,0,0,0,0,0,0,0,6,0,9,0,5,0,0,4,0,0,0,0,2,0,0,0,7,0,10,0,0,0,8]
def t855 : GTree 40 := .f0 38 t854
def t856 : GTree 40 := .f0 36 t855
def t857 : GTree 40 := .f0 31 t856
def t858 : GTree 40 := .f0 18 t857
def t859 : GTree 40 := .f0 16 t858
def t860 : GTree 40 := .f0 15 t859
def t861 : GTree 40 := .f0 14 t860
def t862 : GTree 40 := .f0 13 t861
def t863 : GTree 40 := .f0 12 t862
def t864 : GTree 40 := .f0 11 t863
def t865 : GTree 40 := .f0 10 t864
def t866 : GTree 40 := .f0 9 t865
def t867 : GTree 40 := .f0 5 t866
def t868 : GTree 40 := .f0 37 t867
def t869 : GTree 40 := .f0 34 t868
def t870 : GTree 40 := .f0 32 t869
def t871 : GTree 40 := .f0 30 t870
def t872 : GTree 40 := .f0 28 t871
def t873 : GTree 40 := .f0 27 t872
def t874 : GTree 40 := .f0 25 t873
def t875 : GTree 40 := .f0 23 t874
def t876 : GTree 40 := .f0 22 t875
def t877 : GTree 40 := .f0 20 t876
def t878 : GTree 40 := .b2 3 t853 t877
def t879 : GTree 40 := .b2 7 t829 t878
def t880 : GTree 40 := .base 0 [0,0,0,0,0,0,0,0,0,0,6,1,0,0,0,0,0,9,3,0,0,0,0,8,2,0,0,0,0,5,7,0,0,0,0,0,10,0,4,0]
def t881 : GTree 40 := .f0 39 t880
def t882 : GTree 40 := .f1 12 t881
def t883 : GTree 40 := .f0 35 t882
def t884 : GTree 40 := .f0 34 t883
def t885 : GTree 40 := .f0 32 t884
def t886 : GTree 40 := .f0 28 t885
def t887 : GTree 40 := .f0 21 t886
def t888 : GTree 40 := .f0 19 t887
def t889 : GTree 40 := .f0 16 t888
def t890 : GTree 40 := .f0 15 t889
def t891 : GTree 40 := .f0 14 t890
def t892 : GTree 40 := .f0 13 t891
def t893 : GTree 40 := .f0 9 t892
def t894 : GTree 40 := .f0 8 t893
def t895 : GTree 40 := .f0 7 t894
def t896 : GTree 40 := .f0 5 t895
def t897 : GTree 40 := .f0 37 t896
def t898 : GTree 40 := .f0 33 t897
def t899 : GTree 40 := .f0 31 t898
def t900 : GTree 40 := .f0 27 t899
def t901 : GTree 40 := .f0 25 t900
def t902 : GTree 40 := .f0 22 t901
def t903 : GTree 40 := .f0 20 t902
def t904 : GTree 40 := .base 0 [0,0,0,0,6,0,0,3,0,1,0,0,0,0,0,0,0,9,0,0,0,8,0,0,5,0,0,0,0,7,0,0,2,0,4,0,10,0,0,0]
def t905 : GTree 40 := .f0 39 t904
def t906 : GTree 40 := .f1 19 t905
def t907 : GTree 40 := .f0 38 t906
def t908 : GTree 40 := .f0 35 t907
def t909 : GTree 40 := .f0 18 t908
def t910 : GTree 40 := .f0 16 t909
def t911 : GTree 40 := .f0 15 t910
def t912 : GTree 40 := .f0 14 t911
def t913 : GTree 40 := .f0 13 t912
def t914 : GTree 40 := .f0 12 t913
def t915 : GTree 40 := .f0 11 t914
def t916 : GTree 40 := .f0 10 t915
def t917 : GTree 40 := .f0 8 t916
def t918 : GTree 40 := .f0 37 t917
def t919 : GTree 40 := .f0 33 t918
def t920 : GTree 40 := .f0 31 t919
def t921 : GTree 40 := .f0 30 t920
def t922 : GTree 40 := .f0 28 t921
def t923 : GTree 40 := .f0 27 t922
def t924 : GTree 40 := .f0 25 t923
def t925 : GTree 40 := .f0 23 t924
def t926 : GTree 40 := .f0 22 t925
def t927 : GTree 40 := .f0 20 t926
def t928 : GTree 40 := .b2 3 t903 t927
def t929 : GTree 40 := .base 0 [0,0,0,0,0,0,0,0,0,0,6,0,3,0,0,0,1,9,0,0,0,0,0,8,0,0,0,0,2,0,5,0,4,0,0,7,10,0,0,0]
def t930 : GTree 40 := .f0 38 t929
def t931 : GTree 40 := .f1 18 t930
def t932 : GTree 40 := .f0 34 t931
def t933 : GTree 40 := .f0 24 t932
def t934 : GTree 40 := .f0 19 t933
def t935 : GTree 40 := .f0 15 t934
def t936 : GTree 40 := .f0 14 t935
def t937 : GTree 40 := .f0 13 t936
def t938 : GTree 40 := .f0 11 t937
def t939 : GTree 40 := .f0 9 t938
def t940 : GTree 40 := .f0 8 t939
def t941 : GTree 40 := .f0 7 t940
def t942 : GTree 40 := .f0 5 t941
def t943 : GTree 40 := .f0 39 t942
def t944 : GTree 40 := .f0 37 t943
def t945 : GTree 40 := .f0 33 t944
def t946 : GTree 40 := .f0 31 t945
def t947 : GTree 40 := .f0 29 t946
def t948 : GTree 40 := .f0 27 t947
def t949 : GTree 40 := .f0 25 t948
def t950 : GTree 40 := .f0 22 t949
def t951 : GTree 40 := .f0 21 t950
def t952 : GTree 40 := .f0 20 t951
def t953 : GTree 40 := .base 0 [0,0,0,0,0,7,0,0,2,8,4,10,5,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,6,0,0,3,9,0,0,0]
def t954 : GTree 40 := .f0 38 t953
def t955 : GTree 40 := .f0 34 t954
def t956 : GTree 40 := .f0 19 t955
def t957 : GTree 40 := .f0 18 t956
def t958 : GTree 40 := .f0 17 t957
def t959 : GTree 40 := .f0 16 t958
def t960 : GTree 40 := .f0 15 t959
def t961 : GTree 40 := .f0 14 t960
def t962 : GTree 40 := .f0 13 t961
def t963 : GTree 40 := .f0 7 t962
def t964 : GTree 40 := .f0 3 t963
def t965 : GTree 40 := .f0 39 t964
def t966 : GTree 40 := .f0 37 t965
def t967 : GTree 40 := .f0 33 t966
def t968 : GTree 40 := .f0 31 t967
def t969 : GTree 40 := .f0 29 t968
def t970 : GTree 40 := .f0 27 t969
def t971 : GTree 40 := .f0 25 t970
def t972 : GTree 40 := .f0 24 t971
def t973 : GTree 40 := .f0 23 t972
def t974 : GTree 40 := .f0 22 t973
def t975 : GTree 40 := .f0 21 t974
def t976 : GTree 40 := .f0 20 t975
def t977 : GTree 40 := .b2 4 t952 t976
def t978 : GTree 40 := .b2 2 t928 t977
def t979 : GTree 40 := .b2 6 t879 t978
def t980 : GTree 40 := .base 0 [0,0,0,0,1,0,0,0,0,3,0,9,0,0,0,0,0,0,6,0,0,0,5,0,7,0,0,0,2,4,8,10,0,0,0,0,0,0,0,0]
def t981 : GTree 40 := .f0 39 t980
def t982 : GTree 40 := .f1 19 t981
def t983 : GTree 40 := .f0 38 t982
def t984 : GTree 40 := .f0 36 t983
def t985 : GTree 40 := .f0 35 t984
def t986 : GTree 40 := .f0 34 t985
def t987 : GTree 40 := .f0 17 t986
def t988 : GTree 40 := .f0 33 t987
def t989 : GTree 40 := .f0 16 t988
def t990 : GTree 40 := .f0 32 t989
def t991 : GTree 40 := .f0 23 t990
def t992 : GTree 40 := .f0 15 t991
def t993 : GTree 40 := .f0 14 t992
def t994 : GTree 40 := .f0 13 t993
def t995 : GTree 40 := .f0 12 t994
def t996 : GTree 40 := .f0 8 t995
def t997 : GTree 40 := .f0 37 t996
def t998 : GTree 40 := .f0 27 t997
def t999 : GTree 40 := .f0 25 t998
def t1000 : GTree 40 := .f0 20 t999
def t1001 : GTree 40 := .f0 10 t1000
def t1002 : GTree 40 := .f0 7 t1001
def t1003 : GTree 40 := .f0 6 t1002
def t1004 : GTree 40 := .base 0 [0,0,0,0,9,0,0,0,0,3,0,1,0,0,0,0,0,0,6,0,0,0,5,8,0,0,0,0,2,0,0,10,0,0,0,0,4,0,7,0]
def t1005 : GTree 40 := .f0 19 t1004
def t1006 : GTree 40 := .f0 39 t1005
def t1007 : GTree 40 := .f0 35 t1006
def t1008 : GTree 40 := .f0 34 t1007
def t1009 : GTree 40 := .f0 17 t1008
def t1010 : GTree 40 := .f0 33 t1009
def t1011 : GTree 40 := .f0 29 t1010
def t1012 : GTree 40 := .f0 16 t1011
def t1013 : GTree 40 := .f0 15 t1012
def t1014 : GTree 40 := .f0 14 t1013
def t1015 : GTree 40 := .f0 13 t1014
def t1016 : GTree 40 := .f0 12 t1015
def t1017 : GTree 40 := .f0 8 t1016
def t1018 : GTree 40 := .f0 37 t1017
def t1019 : GTree 40 := .f0 32 t1018
def t1020 : GTree 40 := .f0 30 t1019
def t1021 : GTree 40 := .f0 27 t1020
def t1022 : GTree 40 := .f0 25 t1021
def t1023 : GTree 40 := .f0 24 t1022
def t1024 : GTree 40 := .f0 20 t1023
def t1025 : GTree 40 := .f0 10 t1024
def t1026 : GTree 40 := .f0 7 t1025
def t1027 : GTree 40 := .f0 6 t1026
def t1028 : GTree 40 := .b2 5 t1003 t1027
def t1029 : GTree 40 := .base 0 [0,0,0,0,9,0,0,0,0,0,0,0,3,1,6,0,0,0,0,0,0,0,0,8,0,0,0,0,2,10,5,0,4,7,0,0,0,0,0,0]
def t1030 : GTree 40 := .f0 39 t1029
def t1031 : GTree 40 := .f0 38 t1030
def t1032 : GTree 40 := .f0 16 t1031
def t1033 : GTree 40 := .f0 36 t1032
def t1034 : GTree 40 := .f0 35 t1033
def t1035 : GTree 40 := .f0 34 t1034
def t1036 : GTree 40 := .f0 31 t1035
def t1037 : GTree 40 := .f0 24 t1036
def t1038 : GTree 40 := .f0 19 t1037
def t1039 : GTree 40 := .f0 18 t1038
def t1040 : GTree 40 := .f0 11 t1039
def t1041 : GTree 40 := .f0 9 t1040
def t1042 : GTree 40 := .f0 8 t1041
def t1043 : GTree 40 := .f0 37 t1042
def t1044 : GTree 40 := .f0 27 t1043
def t1045 : GTree 40 := .f0 25 t1044
def t1046 : GTree 40 := .f0 20 t1045
def t1047 : GTree 40 := .f0 17 t1046
def t1048 : GTree 40 := .f0 15 t1047
def t1049 : GTree 40 := .f0 10 t1048
def t1050 : GTree 40 := .f0 7 t1049
def t1051 : GTree 40 := .f0 6 t1050
def t1052 : GTree 40 := .f0 5 t1051
def t1053 : GTree 40 := .base 0 [0,0,0,0,0,0,0,0,1,0,0,0,9,6,0,0,0,0,0,3,0,0,0,2,0,0,0,0,10,5,0,8,0,7,0,4,0,0,0,0]
def t1054 : GTree 40 := .f0 39 t1053
def t1055 : GTree 40 := .f0 38 t1054
def t1056 : GTree 40 := .f0 11 t1055
def t1057 : GTree 40 := .f0 36 t1056
def t1058 : GTree 40 := .f0 14 t1057
def t1059 : GTree 40 := .f0 34 t1058
def t1060 : GTree 40 := .f0 32 t1059
def t1061 : GTree 40 := .f0 30 t1060
def t1062 : GTree 40 := .f0 24 t1061
def t1063 : GTree 40 := .f0 9 t1062
def t1064 : GTree 40 := .f0 37 t1063
def t1065 : GTree 40 := .f0 27 t1064
def t1066 : GTree 40 := .f0 25 t1065
def t1067 : GTree 40 := .f0 20 t1066
def t1068 : GTree 40 := .f0 18 t1067
def t1069 : GTree 40 := .f0 17 t1068
def t1070 : GTree 40 := .f0 16 t1069
def t1071 : GTree 40 := .f0 15 t1070
def t1072 : GTree 40 := .f0 10 t1071
def t1073 : GTree 40 := .f0 7 t1072
def t1074 : GTree 40 := .f0 6 t1073
def t1075 : GTree 40 := .f0 5 t1074
def t1076 : GTree 40 := .f0 3 t1075
def t1077 : GTree 40 := .b2 22 t1052 t1076
def t1078 : GTree 40 := .b2 21 t1028 t1077
def t1079 : GTree 40 := .base 0 [0,0,0,0,0,0,0,0,6,1,0,0,0,0,9,0,3,0,0,0,0,0,0,0,5,0,0,0,7,0,8,0,2,0,10,0,4,0,0,0]
def t1080 : GTree 40 := .f0 38 t1079
def t1081 : GTree 40 := .f1 19 t1080
def t1082 : GTree 40 := .f0 35 t1081
def t1083 : GTree 40 := .f0 33 t1082
def t1084 : GTree 40 := .f0 15 t1083
def t1085 : GTree 40 := .f0 31 t1084
def t1086 : GTree 40 := .f0 23 t1085
def t1087 : GTree 40 := .f0 18 t1086
def t1088 : GTree 40 := .f0 17 t1087
def t1089 : GTree 40 := .f0 13 t1088
def t1090 : GTree 40 := .f0 12 t1089
def t1091 : GTree 40 := .f0 11 t1090
def t1092 : GTree 40 := .f0 39 t1091
def t1093 : GTree 40 := .f0 37 t1092
def t1094 : GTree 40 := .f0 29 t1093
def t1095 : GTree 40 := .f0 27 t1094
def t1096 : GTree 40 := .f0 25 t1095
def t1097 : GTree 40 := .f0 22 t1096
def t1098 : GTree 40 := .f0 21 t1097
def t1099 : GTree 40 := .f0 20 t1098
def t1100 : GTree 40 := .f0 10 t1099
def t1101 : GTree 40 := .f0 7 t1100
def t1102 : GTree 40 := .f0 6 t1101
def t1103 : GTree 40 := .base 0 [0,0,0,0,0,0,0,0,0,9,0,1,0,0,3,0,0,0,0,6,0,0,0,0,0,0,0,0,8,0,4,0,0,2,0,5,10,0,7,0]
def t1104 : GTree 40 := .f0 34 t1103
def t1105 : GTree 40 := .f0 16 t1104
def t1106 : GTree 40 := .f0 32 t1105
def t1107 : GTree 40 := .f0 18 t1106
def t1108 : GTree 40 := .f0 17 t1107
def t1109 : GTree 40 := .f0 15 t1108
def t1110 : GTree 40 := .f0 13 t1109
def t1111 : GTree 40 := .f0 12 t1110
def t1112 : GTree 40 := .f0 5 t1111
def t1113 : GTree 40 := .f0 39 t1112
def t1114 : GTree 40 := .f0 37 t1113
def t1115 : GTree 40 := .f0 31 t1114
def t1116 : GTree 40 := .f0 29 t1115
def t1117 : GTree 40 := .f0 27 t1116
def t1118 : GTree 40 := .f0 25 t1117
def t1119 : GTree 40 := .f0 24 t1118
def t1120 : GTree 40 := .f0 23 t1119
def t1121 : GTree 40 := .f0 22 t1120
def t1122 : GTree 40 := .f0 21 t1121
def t1123 : GTree 40 := .f0 20 t1122
def t1124 : GTree 40 := .f0 10 t1123
def t1125 : GTree 40 := .f0 7 t1124
def t1126 : GTree 40 := .f0 6 t1125
def t1127 : GTree 40 := .b2 4 t1102 t1126
def t1128 : GTree 40 := .base 0 [0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,9,0,6,3,0,0,0,0,0,2,0,0,0,0,0,0,10,0,5,0,8,7,0,4,0]
def t1129 : GTree 40 := .f0 34 t1128
def t1130 : GTree 40 := .f0 16 t1129
def t1131 : GTree 40 := .f0 32 t1130
def t1132 : GTree 40 := .f0 19 t1131
def t1133 : GTree 40 := .f0 14 t1132
def t1134 : GTree 40 := .f0 13 t1133
def t1135 : GTree 40 := .f0 12 t1134
def t1136 : GTree 40 := .f0 9 t1135
def t1137 : GTree 40 := .f0 5 t1136
def t1138 : GTree 40 := .f0 39 t1137
def t1139 : GTree 40 := .f0 37 t1138
def t1140 : GTree 40 := .f0 30 t1139
def t1141 : GTree 40 := .f0 29 t1140
def t1142 : GTree 40 := .f0 28 t1141
def t1143 : GTree 40 := .f0 27 t1142
def t1144 : GTree 40 := .f0 25 t1143
def t1145 : GTree 40 := .f0 23 t1144
def t1146 : GTree 40 := .f0 22 t1145
def t1147 : GTree 40 := .f0 21 t1146
def t1148 : GTree 40 := .f0 20 t1147
def t1149 : GTree 40 := .f0 10 t1148
def t1150 : GTree 40 := .f0 7 t1149
def t1151 : GTree 40 := .f0 6 t1150
def t1152 : GTree 40 := .base 0 [0,0,0,0,0,0,0,0,2,7,0,0,0,8,0,4,0,5,10,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,3,6,0,9,0]
def t1153 : GTree 40 := .f0 32 t1152
def t1154 : GTree 40 := .f0 19 t1153
def t1155 : GTree 40 := .f0 16 t1154
def t1156 : GTree 40 := .f0 14 t1155
def t1157 : GTree 40 := .f0 12 t1156
def t1158 : GTree 40 := .f0 11 t1157
def t1159 : GTree 40 := .f0 5 t1158
def t1160 : GTree 40 := .f0 39 t1159
def t1161 : GTree 40 := .f0 37 t1160
def t1162 : GTree 40 := .f0 31 t1161
def t1163 : GTree 40 := .f0 30 t1162
def t1164 : GTree 40 := .f0 29 t1163
def t1165 : GTree 40 := .f0 28 t1164
def t1166 : GTree 40 := .f0 27 t1165
def t1167 : GTree 40 := .f0 25 t1166
def t1168 : GTree 40 := .f0 24 t1167
def t1169 : GTree 40 := .f0 23 t1168
def t1170 : GTree 40 := .f0 22 t1169
def t1171 : GTree 40 := .f0 21 t1170
def t1172 : GTree 40 := .f0 20 t1171
def t1173 : GTree 40 := .f0 10 t1172
def t1174 : GTree 40 := .f0 7 t1173
def t1175 : GTree 40 := .f0 6 t1174
def t1176 : GTree 40 := .b2 4 t1151 t1175
def t1177 : GTree 40 := .b2 3 t1127 t1176
def t1178 : GTree 40 := .b2 2 t1078 t1177
def t1179 : GTree 40 := .b2 26 t979 t1178
def t1180 : GTree 40 := .base 0 [0,0,0,0,0,0,0,6,3,0,9,0,0,0,1,0,0,0,0,0,0,0,0,5,2,0,0,0,0,8,10,0,0,4,7,0,0,0,0,0]
def t1181 : GTree 40 := .f0 39 t1180
def t1182 : GTree 40 := .f0 17 t1181
def t1183 : GTree 40 := .f0 36 t1182
def t1184 : GTree 40 := .f0 35 t1183
def t1185 : GTree 40 := .f0 32 t1184
def t1186 : GTree 40 := .f0 31 t1185
def t1187 : GTree 40 := .f0 18 t1186
def t1188 : GTree 40 := .f0 22 t1187
def t1189 : GTree 40 := .f0 19 t1188
def t1190 : GTree 40 := .f0 16 t1189
def t1191 : GTree 40 := .f0 15 t1190
def t1192 : GTree 40 := .f0 13 t1191
def t1193 : GTree 40 := .f0 12 t1192
def t1194 : GTree 40 := .f0 11 t1193
def t1195 : GTree 40 := .f0 9 t1194
def t1196 : GTree 40 := .f0 38 t1195
def t1197 : GTree 40 := .f0 37 t1196
def t1198 : GTree 40 := .f0 28 t1197
def t1199 : GTree 40 := .f0 27 t1198
def t1200 : GTree 40 := .f0 26 t1199
def t1201 : GTree 40 := .f0 25 t1200
def t1202 : GTree 40 := .f0 21 t1201
def t1203 : GTree 40 := .f0 20 t1202
def t1204 : GTree 40 := .base 0 [0,0,0,0,0,0,0,0,0,0,9,0,0,0,1,0,0,0,3,6,0,0,0,5,2,0,0,0,0,8,10,0,0,0,4,0,0,0,0,7]
def t1205 : GTree 40 := .f0 36 t1204
def t1206 : GTree 40 := .f1 16 t1205
def t1207 : GTree 40 := .f0 35 t1206
def t1208 : GTree 40 := .f0 32 t1207
def t1209 : GTree 40 := .f0 17 t1208
def t1210 : GTree 40 := .f0 15 t1209
def t1211 : GTree 40 := .f0 13 t1210
def t1212 : GTree 40 := .f0 12 t1211
def t1213 : GTree 40 := .f0 11 t1212
def t1214 : GTree 40 := .f0 9 t1213
def t1215 : GTree 40 := .f0 8 t1214
def t1216 : GTree 40 := .f0 7 t1215
def t1217 : GTree 40 := .f0 38 t1216
def t1218 : GTree 40 := .f0 37 t1217
def t1219 : GTree 40 := .f0 33 t1218
def t1220 : GTree 40 := .f0 31 t1219
def t1221 : GTree 40 := .f0 28 t1220
def t1222 : GTree 40 := .f0 27 t1221
def t1223 : GTree 40 := .f0 26 t1222
def t1224 : GTree 40 := .f0 25 t1223
def t1225 : GTree 40 := .f0 22 t1224
def t1226 : GTree 40 := .f0 21 t1225
def t1227 : GTree 40 := .f0 20 t1226
def t1228 : GTree 40 := .b2 6 t1203 t1227
def t1229 : GTree 40 := .base 0 [0,0,0,0,0,0,0,0,0,6,0,0,9,0,1,0,0,3,0,0,0,0,0,2,0,0,0,0,0,5,0,8,0,4,7,0,0,0,0,10]
def t1230 : GTree 40 := .f0 36 t1229
def t1231 : GTree 40 := .f0 19 t1230
def t1232 : GTree 40 := .f0 35 t1231
def t1233 : GTree 40 := .f0 18 t1232
def t1234 : GTree 40 := .f0 22 t1233
def t1235 : GTree 40 := .f0 16 t1234
def t1236 : GTree 40 := .f0 15 t1235
def t1237 : GTree 40 := .f0 13 t1236
def t1238 : GTree 40 := .f0 11 t1237
def t1239 : GTree 40 := .f0 10 t1238
def t1240 : GTree 40 := .f0 8 t1239
def t1241 : GTree 40 := .f0 6 t1240
def t1242 : GTree 40 := .f0 38 t1241
def t1243 : GTree 40 := .f0 37 t1242
def t1244 : GTree 40 := .f0 32 t1243
def t1245 : GTree 40 := .f0 30 t1244
def t1246 : GTree 40 := .f0 28 t1245
def t1247 : GTree 40 := .f0 27 t1246
def t1248 : GTree 40 := .f0 26 t1247
def t1249 : GTree 40 := .f0 25 t1248
def t1250 : GTree 40 := .f0 24 t1249
def t1251 : GTree 40 := .f0 21 t1250
def t1252 : GTree 40 := .f0 20 t1251
def t1253 : GTree 40 := .base 0 [0,0,0,0,0,0,10,0,0,2,5,4,0,8,0,7,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,9,0,6,3,0,0,0]
def t1254 : GTree 40 := .f0 19 t1253
def t1255 : GTree 40 := .f0 39 t1254
def t1256 : GTree 40 := .f0 22 t1255
def t1257 : GTree 40 := .f0 18 t1256
def t1258 : GTree 40 := .f0 17 t1257
def t1259 : GTree 40 := .f0 16 t1258
def t1260 : GTree 40 := .f0 14 t1259
def t1261 : GTree 40 := .f0 12 t1260
def t1262 : GTree 40 := .f0 8 t1261
def t1263 : GTree 40 := .f0 4 t1262
def t1264 : GTree 40 := .f0 38 t1263
def t1265 : GTree 40 := .f0 37 t1264
def t1266 : GTree 40 := .f0 34 t1265
def t1267 : GTree 40 := .f0 32 t1266
def t1268 : GTree 40 := .f0 30 t1267
def t1269 : GTree 40 := .f0 28 t1268
def t1270 : GTree 40 := .f0 27 t1269
def t1271 : GTree 40 := .f0 26 t1270
def t1272 : GTree 40 := .f0 25 t1271
def t1273 : GTree 40 := .f0 24 t1272
def t1274 : GTree 40 := .f0 23 t1273
def t1275 : GTree 40 := .f0 21 t1274
def t1276 : GTree 40 := .f0 20 t1275
def t1277 : GTree 40 := .b2 7 t1252 t1276
def t1278 : GTree 40 := .b2 5 t1228 t1277
def t1279 : GTree 40 := .base 0 [0,0,0,0,0,0,0,0,3,6,0,0,9,0,1,0,0,0,0,0,0,0,0,0,2,0,0,0,0,5,0,8,0,4,7,0,0,0,0,10]
def t1280 : GTree 40 := .f0 36 t1279
def t1281 : GTree 40 := .f0 35 t1280
def t1282 : GTree 40 := .f0 32 t1281
def t1283 : GTree 40 := .f0 19 t1282
def t1284 : GTree 40 := .f0 18 t1283
def t1285 : GTree 40 := .f0 17 t1284
def t1286 : GTree 40 := .f0 16 t1285
def t1287 : GTree 40 := .f0 15 t1286
def t1288 : GTree 40 := .f0 13 t1287
def t1289 : GTree 40 := .f0 11 t1288
def t1290 : GTree 40 := .f0 10 t1289
def t1291 : GTree 40 := .f0 7 t1290
def t1292 : GTree 40 := .f0 38 t1291
def t1293 : GTree 40 := .f0 37 t1292
def t1294 : GTree 40 := .f0 30 t1293
def t1295 : GTree 40 := .f0 28 t1294
def t1296 : GTree 40 := .f0 27 t1295
def t1297 : GTree 40 := .f0 26 t1296
def t1298 : GTree 40 := .f0 25 t1297
def t1299 : GTree 40 := .f0 23 t1298
def t1300 : GTree 40 := .f0 22 t1299
def t1301 : GTree 40 := .f0 21 t1300
def t1302 : GTree 40 := .f0 20 t1301
def t1303 : GTree 40 := .base 0 [0,0,0,0,8,0,0,7,2,0,0,0,0,10,0,0,4,0,5,0,0,0,0,0,0,0,0,0,0,9,0,0,1,0,6,3,0,0,0,0]
def t1304 : GTree 40 := .f0 19 t1303
def t1305 : GTree 40 := .f0 39 t1304
def t1306 : GTree 40 := .f0 36 t1305
def t1307 : GTree 40 := .f0 17 t1306
def t1308 : GTree 40 := .f0 15 t1307
def t1309 : GTree 40 := .f0 14 t1308
def t1310 : GTree 40 := .f0 12 t1309
def t1311 : GTree 40 := .f0 11 t1310
def t1312 : GTree 40 := .f0 10 t1311
def t1313 : GTree 40 := .f0 9 t1312
def t1314 : GTree 40 := .f0 38 t1313
def t1315 : GTree 40 := .f0 37 t1314
def t1316 : GTree 40 := .f0 33 t1315
def t1317 : GTree 40 := .f0 31 t1316
def t1318 : GTree 40 := .f0 30 t1317
def t1319 : GTree 40 := .f0 28 t1318
def t1320 : GTree 40 := .f0 27 t1319
def t1321 : GTree 40 := .f0 26 t1320
def t1322 : GTree 40 := .f0 25 t1321
def t1323 : GTree 40 := .f0 23 t1322
def t1324 : GTree 40 := .f0 22 t1323
def t1325 : GTree 40 := .f0 21 t1324
def t1326 : GTree 40 := .f0 20 t1325
def t1327 : GTree 40 := .b2 6 t1302 t1326
def t1328 : GTree 40 := .f0 34 t1255
def t1329 : GTree 40 := .f0 18 t1328
def t1330 : GTree 40 := .f0 17 t1329
def t1331 : GTree 40 := .f0 16 t1330
def t1332 : GTree 40 := .f0 14 t1331
def t1333 : GTree 40 := .f0 8 t1332
def t1334 : GTree 40 := .f0 7 t1333
def t1335 : GTree 40 := .f0 4 t1334
def t1336 : GTree 40 := .f0 38 t1335
def t1337 : GTree 40 := .f0 37 t1336
def t1338 : GTree 40 := .f0 32 t1337
def t1339 : GTree 40 := .f0 30 t1338
def t1340 : GTree 40 := .f0 28 t1339
def t1341 : GTree 40 := .f0 27 t1340
def t1342 : GTree 40 := .f0 26 t1341
def t1343 : GTree 40 := .f0 25 t1342
def t1344 : GTree 40 := .f0 24 t1343
def t1345 : GTree 40 := .f0 23 t1344
def t1346 : GTree 40 := .f0 22 t1345
def t1347 : GTree 40 := .f0 21 t1346
def t1348 : GTree 40 := .f0 20 t1347
def t1349 : GTree 40 := .base 0 [0,0,0,0,0,0,0,0,0,0,7,0,0,5,8,10,4,2,0,0,0,0,0,0,0,0,0,0,0,6,0,0,0,0,9,1,3,0,0,0]
def t1350 : GTree 40 := .f0 19 t1349
def t1351 : GTree 40 := .f0 18 t1350
def t1352 : GTree 40 := .f0 11 t1351
def t1353 : GTree 40 := .f0 9 t1352
def t1354 : GTree 40 := .f0 8 t1353
def t1355 : GTree 40 := .f0 7 t1354
def t1356 : GTree 40 := .f0 6 t1355
def t1357 : GTree 40 := .f0 4 t1356
def t1358 : GTree 40 := .f0 39 t1357
def t1359 : GTree 40 := .f0 38 t1358
def t1360 : GTree 40 := .f0 37 t1359
def t1361 : GTree 40 := .f0 32 t1360
def t1362 : GTree 40 := .f0 31 t1361
def t1363 : GTree 40 := .f0 30 t1362
def t1364 : GTree 40 := .f0 28 t1363
def t1365 : GTree 40 := .f0 27 t1364
def t1366 : GTree 40 := .f0 26 t1365
def t1367 : GTree 40 := .f0 25 t1366
def t1368 : GTree 40 := .f0 24 t1367
def t1369 : GTree 40 := .f0 23 t1368
def t1370 : GTree 40 := .f0 22 t1369
def t1371 : GTree 40 := .f0 21 t1370
def t1372 : GTree 40 := .f0 20 t1371
def t1373 : GTree 40 := .b2 12 t1348 t1372
def t1374 : GTree 40 := .b2 5 t1327 t1373
def t1375 : GTree 40 := .b2 3 t1278 t1374
def t1376 : GTree 40 := .base 0 [0,0,0,0,0,0,0,6,3,0,0,9,0,0,1,0,0,0,0,0,0,0,0,5,2,0,0,0,0,0,10,8,0,4,7,0,0,0,0,0]
def t1377 : GTree 40 := .f0 36 t1376
def t1378 : GTree 40 := .f0 35 t1377
def t1379 : GTree 40 := .f0 32 t1378
def t1380 : GTree 40 := .f0 19 t1379
def t1381 : GTree 40 := .f0 18 t1380
def t1382 : GTree 40 := .f0 17 t1381
def t1383 : GTree 40 := .f0 16 t1382
def t1384 : GTree 40 := .f0 15 t1383
def t1385 : GTree 40 := .f0 13 t1384
def t1386 : GTree 40 := .f0 12 t1385
def t1387 : GTree 40 := .f0 10 t1386
def t1388 : GTree 40 := .f0 5 t1387
def t1389 : GTree 40 := .f0 39 t1388
def t1390 : GTree 40 := .f0 38 t1389
def t1391 : GTree 40 := .f0 37 t1390
def t1392 : GTree 40 := .f0 29 t1391
def t1393 : GTree 40 := .f0 28 t1392
def t1394 : GTree 40 := .f0 27 t1393
def t1395 : GTree 40 := .f0 26 t1394
def t1396 : GTree 40 := .f0 25 t1395
def t1397 : GTree 40 := .f0 22 t1396
def t1398 : GTree 40 := .f0 21 t1397
def t1399 : GTree 40 := .f0 20 t1398
def t1400 : GTree 40 := .base 0 [0,0,0,0,8,10,0,0,0,0,7,4,0,0,0,0,0,2,0,5,0,0,0,0,9,0,0,0,0,0,1,0,0,0,0,6,3,0,0,0]
def t1401 : GTree 40 := .f0 18 t1400
def t1402 : GTree 40 := .f0 34 t1401
def t1403 : GTree 40 := .f0 32 t1402
def t1404 : GTree 40 := .f0 16 t1403
def t1405 : GTree 40 := .f0 15 t1404
def t1406 : GTree 40 := .f0 14 t1405
def t1407 : GTree 40 := .f0 13 t1406
def t1408 : GTree 40 := .f0 12 t1407
def t1409 : GTree 40 := .f0 8 t1408
def t1410 : GTree 40 := .f0 7 t1409
def t1411 : GTree 40 := .f0 39 t1410
def t1412 : GTree 40 := .f0 38 t1411
def t1413 : GTree 40 := .f0 37 t1412
def t1414 : GTree 40 := .f0 33 t1413
def t1415 : GTree 40 := .f0 31 t1414
def t1416 : GTree 40 := .f0 29 t1415
def t1417 : GTree 40 := .f0 28 t1416
def t1418 : GTree 40 := .f0 27 t1417
def t1419 : GTree 40 := .f0 26 t1418
def t1420 : GTree 40 := .f0 25 t1419
def t1421 : GTree 40 := .f0 22 t1420
def t1422 : GTree 40 := .f0 21 t1421
def t1423 : GTree 40 := .f0 20 t1422
def t1424 : GTree 40 := .b2 6 t1399 t1423
def t1425 : GTree 40 := .base 0 [0,0,0,0,0,8,4,0,2,0,0,0,10,0,0,7,0,0,5,0,0,0,0,0,0,0,0,0,0,0,0,1,9,3,6,0,0,0,0,0]
def t1426 : GTree 40 := .f0 17 t1425
def t1427 : GTree 40 := .f0 36 t1426
def t1428 : GTree 40 := .f0 35 t1427
def t1429 : GTree 40 := .f0 19 t1428
def t1430 : GTree 40 := .f0 16 t1429
def t1431 : GTree 40 := .f0 14 t1430
def t1432 : GTree 40 := .f0 13 t1431
def t1433 : GTree 40 := .f0 10 t1432
def t1434 : GTree 40 := .f0 7 t1433
def t1435 : GTree 40 := .f0 4 t1434
def t1436 : GTree 40 := .f0 39 t1435
def t1437 : GTree 40 := .f0 38 t1436
def t1438 : GTree 40 := .f0 37 t1437
def t1439 : GTree 40 := .f0 30 t1438
def t1440 : GTree 40 := .f0 29 t1439
def t1441 : GTree 40 := .f0 28 t1440
def t1442 : GTree 40 := .f0 27 t1441
def t1443 : GTree 40 := .f0 26 t1442
def t1444 : GTree 40 := .f0 25 t1443
def t1445 : GTree 40 := .f0 23 t1444
def t1446 : GTree 40 := .f0 22 t1445
def t1447 : GTree 40 := .f0 21 t1446
def t1448 : GTree 40 := .f0 20 t1447
def t1449 : GTree 40 := .base 0 [0,0,0,0,0,8,0,0,0,0,0,0,0,5,7,4,2,0,10,0,0,0,0,0,9,0,0,0,0,0,0,0,0,6,1,3,0,0,0,0]
def t1450 : GTree 40 := .f0 19 t1449
def t1451 : GTree 40 := .f0 17 t1450
def t1452 : GTree 40 := .f0 12 t1451
def t1453 : GTree 40 := .f0 10 t1452
def t1454 : GTree 40 := .f0 8 t1453
def t1455 : GTree 40 := .f0 7 t1454
def t1456 : GTree 40 := .f0 6 t1455
def t1457 : GTree 40 := .f0 4 t1456
def t1458 : GTree 40 := .f0 39 t1457
def t1459 : GTree 40 := .f0 38 t1458
def t1460 : GTree 40 := .f0 37 t1459
def t1461 : GTree 40 := .f0 36 t1460
def t1462 : GTree 40 := .f0 31 t1461
def t1463 : GTree 40 := .f0 30 t1462
def t1464 : GTree 40 := .f0 29 t1463
def t1465 : GTree 40 := .f0 28 t1464
def t1466 : GTree 40 := .f0 27 t1465
def t1467 : GTree 40 := .f0 26 t1466
def t1468 : GTree 40 := .f0 25 t1467
def t1469 : GTree 40 := .f0 23 t1468
def t1470 : GTree 40 := .f0 22 t1469
def t1471 : GTree 40 := .f0 21 t1470
def t1472 : GTree 40 := .f0 20 t1471
def t1473 : GTree 40 := .b2 11 t1448 t1472
def t1474 : GTree 40 := .b2 3 t1424 t1473
def t1475 : GTree 40 := .base 0 [0,0,0,0,8,0,0,0,0,0,7,10,0,0,4,0,0,2,0,5,0,0,0,0,0,0,0,0,0,0,1,9,0,3,0,6,0,0,0,0]
def t1476 : GTree 40 := .f0 16 t1475
def t1477 : GTree 40 := .f0 32 t1476
def t1478 : GTree 40 := .f0 24 t1477
def t1479 : GTree 40 := .f0 15 t1478
def t1480 : GTree 40 := .f0 13 t1479
def t1481 : GTree 40 := .f0 12 t1480
def t1482 : GTree 40 := .f0 8 t1481
def t1483 : GTree 40 := .f0 7 t1482
def t1484 : GTree 40 := .f0 6 t1483
def t1485 : GTree 40 := .f0 5 t1484
def t1486 : GTree 40 := .f0 39 t1485
def t1487 : GTree 40 := .f0 38 t1486
def t1488 : GTree 40 := .f0 37 t1487
def t1489 : GTree 40 := .f0 36 t1488
def t1490 : GTree 40 := .f0 34 t1489
def t1491 : GTree 40 := .f0 29 t1490
def t1492 : GTree 40 := .f0 28 t1491
def t1493 : GTree 40 := .f0 27 t1492
def t1494 : GTree 40 := .f0 26 t1493
def t1495 : GTree 40 := .f0 25 t1494
def t1496 : GTree 40 := .f0 22 t1495
def t1497 : GTree 40 := .f0 21 t1496
def t1498 : GTree 40 := .f0 20 t1497
def t1499 : GTree 40 := .base 0 [0,0,0,0,2,4,5,0,0,0,0,0,0,7,0,8,10,0,0,0,0,0,0,0,3,0,0,0,0,0,0,0,1,6,0,9,0,0,0,0]
def t1500 : GTree 40 := .f0 19 t1499
def t1501 : GTree 40 := .f0 17 t1500
def t1502 : GTree 40 := .f0 14 t1501
def t1503 : GTree 40 := .f0 12 t1502
def t1504 : GTree 40 := .f0 11 t1503
def t1505 : GTree 40 := .f0 10 t1504
def t1506 : GTree 40 := .f0 8 t1505
def t1507 : GTree 40 := .f0 7 t1506
def t1508 : GTree 40 := .f0 39 t1507
def t1509 : GTree 40 := .f0 38 t1508
def t1510 : GTree 40 := .f0 37 t1509
def t1511 : GTree 40 := .f0 36 t1510
def t1512 : GTree 40 := .f0 34 t1511
def t1513 : GTree 40 := .f0 30 t1512
def t1514 : GTree 40 := .f0 29 t1513
def t1515 : GTree 40 := .f0 28 t1514
def t1516 : GTree 40 := .f0 27 t1515
def t1517 : GTree 40 := .f0 26 t1516
def t1518 : GTree 40 := .f0 25 t1517
def t1519 : GTree 40 := .f0 23 t1518
def t1520 : GTree 40 := .f0 22 t1519
def t1521 : GTree 40 := .f0 21 t1520
def t1522 : GTree 40 := .f0 20 t1521
def t1523 : GTree 40 := .b2 3 t1498 t1522
def t1524 : GTree 40 := .base 0 [0,0,0,0,0,5,10,0,0,0,2,0,7,0,8,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,6,9,0,3,0,0,0,0]
def t1525 : GTree 40 := .f0 19 t1524
def t1526 : GTree 40 := .f0 17 t1525
def t1527 : GTree 40 := .f0 16 t1526
def t1528 : GTree 40 := .f0 13 t1527
def t1529 : GTree 40 := .f0 11 t1528
def t1530 : GTree 40 := .f0 8 t1529
def t1531 : GTree 40 := .f0 7 t1530
def t1532 : GTree 40 := .f0 4 t1531
def t1533 : GTree 40 := .f0 3 t1532
def t1534 : GTree 40 := .f0 39 t1533
def t1535 : GTree 40 := .f0 38 t1534
def t1536 : GTree 40 := .f0 37 t1535
def t1537 : GTree 40 := .f0 36 t1536
def t1538 : GTree 40 := .f0 34 t1537
def t1539 : GTree 40 := .f0 29 t1538
def t1540 : GTree 40 := .f0 28 t1539
def t1541 : GTree 40 := .f0 27 t1540
def t1542 : GTree 40 := .f0 26 t1541
def t1543 : GTree 40 := .f0 25 t1542
def t1544 : GTree 40 := .f0 24 t1543
def t1545 : GTree 40 := .f0 22 t1544
def t1546 : GTree 40 := .f0 21 t1545
def t1547 : GTree 40 := .f0 20 t1546
def t1548 : GTree 40 := .f0 16 t1524
def t1549 : GTree 40 := .f0 13 t1548
def t1550 : GTree 40 := .f0 11 t1549
def t1551 : GTree 40 := .f0 8 t1550
def t1552 : GTree 40 := .f0 39 t1551
def t1553 : GTree 40 := .f0 38 t1552
def t1554 : GTree 40 := .f0 37 t1553
def t1555 : GTree 40 := .f0 36 t1554
def t1556 : GTree 40 := .f0 34 t1555
def t1557 : GTree 40 := .f0 29 t1556
def t1558 : GTree 40 := .f0 28 t1557
def t1559 : GTree 40 := .f0 27 t1558
def t1560 : GTree 40 := .f0 26 t1559
def t1561 : GTree 40 := .f0 25 t1560
def t1562 : GTree 40 := .f0 24 t1561
def t1563 : GTree 40 := .f0 22 t1562
def t1564 : GTree 40 := .f0 21 t1563
def t1565 : GTree 40 := .f0 20 t1564
def t1566 : GTree 40 := .f0 19 t1565
def t1567 : GTree 40 := .f0 17 t1566
def t1568 : GTree 40 := .f0 7 t1567
def t1569 : GTree 40 := .f0 4 t1568
def t1570 : GTree 40 := .f0 3 t1569
def t1571 : GTree 40 := .b2 23 t1547 t1570
def t1572 : GTree 40 := .b2 18 t1523 t1571
def t1573 : GTree 40 := .b2 9 t1474 t1572
def t1574 : GTree 40 := .b2 2 t1375 t1573
def t1575 : GTree 40 := .b2 1 t1179 t1574
def t1576 : GTree 40 := .b2 0 t782 t1575
theorem replay : checkGTree catalog 39 [] Simlowker.Graph9840.edges 51 t1576=true := by decide +kernel
theorem unrestricted (s : Nat) (h : HasCircuitSize 40 Simlowker.Graph9840.target s) : 51 ≤ s := by
  rw [Simlowker.Graph9840.toGraph] at h
  exact checkGTree_sound catalog catalogOk _ _ _ _ replay s h
#print axioms unrestricted
end Simlowker.Graph9840.Anchor

namespace Simlowker.Graph9840.Matching
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds
set_option maxRecDepth 65536
set_option maxHeartbeats 0
abbrev V := Fin 40
def adjMasks : List (BitVec 40) := [137607774208, 275215548416, 550433193984, 1355808768, 2709520384, 5421137920, 10842275840, 21684551680, 43369103360, 86738206720, 173476413440, 346952826880, 693905653760, 288300728320, 576599359488, 53690236928, 107378376704, 214758850560, 429517701120, 859035402240, 40969, 163878, 327756, 655512, 262448, 524897, 1218, 2437, 4874, 9748, 19496, 38992, 77984, 155968, 311936, 623872, 199168, 398337, 796674, 544772]
def adjacent (u v : V) := (adjMasks.getD u.val 0).getLsbD v.val
theorem adj_sym : ∀ u v : V, adjacent u v=adjacent v u := by decide +kernel
def G : SimpleGraph V where
  Adj a b := adjacent a b=true
  symm := ⟨fun a b h => (adj_sym b a).trans h⟩
  loopless := ⟨by decide +kernel⟩
instance : DecidableRel G.Adj := fun a b => inferInstanceAs (Decidable (adjacent a b=true))

theorem degree_ge_two (v : V) : 2 ≤ (G.neighborSet v).ncard := by
  let nbr (u : V) := Finset.univ.filter (fun i : V => adjacent u i=true)
  have eq (u : V) : nbr u=G.neighborFinset u := by
    ext i
    rw [SimpleGraph.mem_neighborFinset]
    change i∈(Finset.univ.filter (fun z : V => adjacent u z=true)) ↔ adjacent u i=true
    simp
  have bound : ∀ u : V, 2 ≤ (nbr u).card := by dsimp only [nbr];decide +kernel
  rw [SimpleGraph.ncard_neighborSet,SimpleGraph.degree,←eq]
  apply bound

def leftSide : Finset V := Finset.univ.filter (fun u : V => u.val<20)
theorem no_isolates : ∀ u : V, ∃ v : V, G.Adj u v := by decide +kernel
theorem distinct_neighborhoods : ∀ a b : V, a≠b → ∃ c : V, ¬(G.Adj a c ↔ G.Adj b c) := by decide +kernel
theorem local_witness : ∀ u v : V, G.Adj u v → ∃ a b : V,
    G.Adj u a ∧ a≠v ∧ G.Adj v b ∧ b≠u ∧ (a=b ∨ ¬G.Adj a b) := by decide +kernel
theorem left_covers : ∀ u v : V, G.Adj u v → u∈leftSide ∨ v∈leftSide := by decide +kernel
def left (i : Fin 20) : V := ⟨i.val,by omega⟩
def right : Fin 20 → V := ![25,26,29,28,31,30,22,27,35,34,37,36,39,38,33,20,32,21,24,23]
theorem matched : ∀ i, G.Adj (left i) (right i) := by decide +kernel
theorem separated : ∀ i j : Fin 20, i≠j →
    left i≠left j ∧ left i≠right j ∧ right i≠left j ∧ right i≠right j := by decide +kernel
theorem coverSize (S : Finset V) (hits : ∀ i, left i∈S ∨ right i∈S) : 20 ≤ S.card := by
  let pick (i : Fin 20) := if left i∈S then left i else right i
  have inj : Function.Injective pick := by
    intro i j eq
    by_contra diff
    obtain ⟨ll,lr,rl,rr⟩ := separated i j diff
    by_cases a : left i∈S <;> by_cases b : left j∈S <;> simp_all [pick]
  have sub : Finset.univ.image pick ⊆ S := by
    intro v hv
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hv
    by_cases hh : left i∈S
    · simpa [pick,hh] using hh
    · simpa [pick,hh] using (hits i).resolve_left hh
  have cnt := Finset.card_le_card sub
  rw [Finset.card_image_of_injective _ inj] at cnt
  simpa using cnt
theorem graph_pairs : ∀ u v : V, Simlowker.Graph9840.target (fun i => decide (i=u ∨ i=v))=true ↔ G.Adj u v := by decide +kernel

theorem monotone_lower (C : Circuit) (hm : Monotone2 C)
    (correct : ∀ x : V → Bool,C.eval (List.ofFn x) = Simlowker.Graph9840.target x) : 59≤C.size := by
  have bound := PEqualNP.Outside.L_meta_3049 40 20 G C no_isolates
    (fun u v ne _ _ _ => distinct_neighborhoods u v ne)
    (fun u v uv _ _ => local_witness u v uv)
    ⟨leftSide,fun u v uv _ _ => left_covers u v uv, by decide +kernel⟩
    (fun S cover => coverSize S (fun i => cover _ _ (matched i) (degree_ge_two _) (degree_ge_two _)))
    hm (fun u v => by rw [correct]; exact graph_pairs u v)
  omega
#print axioms monotone_lower
end Simlowker.Graph9840.Matching

namespace GraphRows9840
abbrev Word := BitVec 780
abbrev V := Fin 40
abbrev E := Fin 95
def words : List Word := [1361129467644139772596366260930300870671, 23384026195933317223614817550864162053564619817200, 100433627742802866025439313547826687350544921564250248322816, 215679573236771490614533254674801120244559414078882946586540484321280, 463168356733585208457512449490370455338328935298357606147535550992520501264384, 248661617741724964344105915917198853998722453924563049496551898409133581942836902756352, 66749594623866822333119464620731308278352784274660974953189389064538966382663943650052763811840, 8958978901961622218362948178659384633627060021871877868669935323720371041161442594655591227464146223104, 601226892231122404378085560399979494038897615710414707832576778188444128839730123020760080262204892292197646336, 20173826571327081125564664401974079423256344381080680012975248000722318587027509789987519945831751143530461264418439168, 338460635846780711336326389085421001640809573798758251524371688752073800835666078834332244607145730123069322845208006958776320, 2839213428319078569429388468993452805430191490965195339834640752998282150431935891779505292740000039173478823493445687399462381551616, 11908522819645794975742073324173620732115672293466481905127129304896649665447096348061522729330699676858062988446437872828491836931182690304, 24973976494005118206273184185376798370405064375621152371475321483974237290346814622077996500524848549146746639281683070644225239125024414306926592, 52374224752361775923610472207160722516876986779334914094890287277713033488297768679676032480588322982828660310462335385216659097612945013478190020034560, 27459138266297686533877273597717697799278504547066536595720107726951679312266382301380637892629235099629131467633542080282763701838238418827221335411735396352, 14396496683399962202229226006093381512507746861658024457540763648907021920657799368140331864726945028326929844277707994546253454849571867197128625594579379600490496, 1886966815914087433281474084356255656384617195216841055439060129309346383109367813559016453087442955996499656794055951801978972318963426570734731836937185490578983354368, 123663313769736435320704146401101994799327494248314821314198241535024116306862204871953472928502721479156868738398352377893737412403867998780710983002026067263129775434104832, 4052137634421618139349135987259504166222541318014481427659427055489268288908808281915675625460861277751530317186388761977825292499011036378178075256800897885069112133990280593408, 2124547919129439634170230183751851664161868919803024179095415445468758083698894550988725339120442715796083367061198662488095374834306063890634437210789179960014043198837505903539789825, 556936427407915618842823627561798897057886100369750232518114301740933342423294318116357166791453513360795309720033156482970883414760388205237097100646005777244008355050442694476622406353168, 72998492945527727740165794826070493418966917502292978309135415814421479956701038135060090210358547955779740084365967238188842503475415798896271253213563560661346469058657172965298695761758798336, 4783992734570871819534372855491457860054011401083312989767317545760143569693396710470068054198580938020347830056542603843010714226433725330402074692415853670483981424324954602888870836843229401612288, 156759481948302057938914906430856122382439998885842999541888248326076986949570222181390817444515975095821162824515825018276358392336462511321036288011565501251116316575309972986082353536155048737784725504, 2568268973696187450015878348170043474061828546029918620397712553576730350456897880055103045119366615748044102806499534460634350421091821721331262609618621435195110593893849120949019689469841596337291956060162, 21037975337234150476714117691436743097210600858733300920833822049030547869220396928927775922225431169581945113605093107434201775777870650751093820624498387188093040045963253178195667777490359054956929556403978272, 86161028636101638895253169345440113748773059380794039571306105838574260530478364659606198923731916945552970676310444838332177590769598312151278119446926913930660875703764334143384149187563682380749050071196501017604, 176414711398333709762963986733635392164332021911574452608399487367018715420573704328802321267297752440946115483505145303584117031101514855844532640177546089477314212257615201877365648632400751269155929347656424097906752, 180560478709064629349245563875784809638521104674153928063717926747412635115087779584826393364175674490554443195265476797763922464648035254177152934943410546927439624772216246444115721181256581167070626350165692408591812608, 92356729178914280230093338729317440263535125620683769470999815291139976242351423159957382915631004657966503911281902717993117566243284179970059317255249335076218130566161566098763712682159371262732646318782652059276256870400, 23597189886972470886046785737320733363130016452031223601019644604791719273269862154484429361303808833772220961214344543223339866517022419514507121918878445677344197951675448827986564618960130353305483980490666585353930305175552, 3008665252408569664465822409993825416905248203872692859201448629408825119715259163922706874532052670122492682272026248666184818843626196586347352043425719627336102559643286834476868134135139919707091878509317987740333259909758976, 191056374983589684074547470997670259768007528263496686219000057007542601861137929117437011917774157660939855535497208131280994325403419780624341678038391961775228417533381042575555828247059039407437825559659864052715439111589068800, 6019087620254323724481034139362122258251935185081561732022941176862673056251866997187606227231020459279261333388156022065113133232885103826667577587565013510958923112762180453851002480884796912568710238570709734743381777452122505216, 93351310324758277927389868986947815848083275516650108471440682979056018857408766057260895438108618186626518798131715444226200724077044652058633616149125477119362741905798775695803882594535926824886510155295709497190244679912733540352, 702138627293351922324240928143446480041452708716043491842059707906723044875105500232854735827516976921858879680363862652731360404874812887062862845863813948857299854691339270719061799219703361795928525883023683779613236235852536872960, 2497249991566402934993363416164494758983753173482241397926011988751185593964852331134296169682813014350296963761859256707604574578199122073187594315753369417776835271582502283456228370980278908374852010788101701122004511302022049300488, 4199610719874842895190449334236188209675980706200734130944777072735769500771335115831826876319458726575075467060671217561186965967513499028713652626574382682984071733887268695304570493966824792675743501132401767715493309906947590324352, 5219664386717833891195788676101171186185858849346473602276775633426787018717103883531270789030290997909907974993820405535933220482680077640974093803547155613714739428410088490007248637422169954848360744687799272978250545833706143092736]
def varWord (v : V) : Word := words.getD v.val 0
def goal : Word := 39614081257132168796771975167
def rneg (r : Fin 685) := 95 + r.val
def adjMasks : List (BitVec 40) := [137607774208, 275215548416, 550433193984, 1355808768, 2709520384, 5421137920, 10842275840, 21684551680, 43369103360, 86738206720, 173476413440, 346952826880, 693905653760, 288300728320, 576599359488, 53690236928, 107378376704, 214758850560, 429517701120, 859035402240, 40969, 163878, 327756, 655512, 262448, 524897, 1218, 2437, 4874, 9748, 19496, 38992, 77984, 155968, 311936, 623872, 199168, 398337, 796674, 544772]
def nb (u : V) := adjMasks.getD u.val 0
def adjacent (u v : V) := (nb u).getLsbD v.val
set_option maxHeartbeats 4000000 in
theorem common : ∀ a b : V, a ≠ b → ∀ c : V, adjacent a c = true → adjacent b c = true →
    c.val = ((nb a &&& nb b).toNat.log2) := by decide +kernel

theorem no_square (a b c d : V) (ab : a ≠ b) (cd : c ≠ d)
    (ac : adjacent a c = true) (ad : adjacent a d = true) (bc : adjacent b c = true) :
    adjacent b d = false := by
  cases h : adjacent b d with
  | false => rfl
  | true => exact False.elim (cd (Fin.ext ((common a b ab c ac bc).trans (common a b ab d ad h).symm)))

end GraphRows9840

namespace GraphUnion9840
variable {α : Type} [DecidableEq α]
abbrev Family (α : Type) := Finset (Finset α)
def cap (pool : Family α) (n : Nat) : Prop :=
  ∀ asks ⊆ pool, (asks.biUnion id).card ≤ asks.card+n

theorem small {pool : Family α} (h : ∀ s∈pool,s.card ≤ 1) : cap pool 0 := by
  intro asks sub
  induction asks using Finset.induction_on with
  | empty => simp
  | @insert a t ha ih =>
    rw [Finset.biUnion_insert,Finset.card_insert_of_notMem ha]
    have ca := h a (sub (Finset.mem_insert_self a t))
    have prev := ih ((Finset.subset_insert a t).trans sub)
    exact (Finset.card_union_le _ _).trans (by simp only [id_eq]; omega)

theorem merge {pool : Family α} {n : Nat} (h : cap pool n) {a b : Finset α}
    (ha : a∈pool) (hb : b∈pool) : cap (insert (a∪b) pool) (n+1) := by
  intro asks sub
  by_cases occurs : a∪b∈asks
  · let rem := asks.erase (a∪b)
    have smaller : rem ⊆ pool := by
      intro s hs
      obtain ⟨ne,mem⟩ := Finset.mem_erase.mp hs
      exact (Finset.mem_insert.mp (sub mem)).resolve_left ne
    let replacement := insert a (insert b rem)
    have hr : replacement ⊆ pool :=
      Finset.insert_subset ha (Finset.insert_subset hb smaller)
    have cov : asks.biUnion id ⊆ replacement.biUnion id := by
      intro x hx
      obtain ⟨s,hs,hx⟩ := Finset.mem_biUnion.mp hx
      by_cases eq : s=a∪b
      · subst s
        rcases Finset.mem_union.mp hx with xa|xb
        · exact Finset.mem_biUnion.mpr ⟨_,Finset.mem_insert_self _ _,xa⟩
        · exact Finset.mem_biUnion.mpr ⟨_,Finset.mem_insert_of_mem (Finset.mem_insert_self _ _),xb⟩
      · exact Finset.mem_biUnion.mpr ⟨s,Finset.mem_insert_of_mem
          (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨eq,hs⟩)),hx⟩
    have size := h replacement hr
    have r1 := Finset.card_insert_le a (insert b rem)
    have r2 := Finset.card_insert_le b rem
    have r3 : rem.card+1=asks.card := Finset.card_erase_add_one occurs
    exact (Finset.card_le_card cov).trans (by dsimp [replacement] at size ⊢; omega)
  · have orig : asks ⊆ pool := fun v hv => (Finset.mem_insert.mp (sub hv)).resolve_left
        (fun eq => occurs (eq ▸ hv))
    exact (h asks orig).trans (by omega)

theorem one {pool : Family α} {n : Nat} (h : cap pool n) {a : Finset α} (ha : a∈pool) :
    a.card ≤ n+1 := by
  simpa [Nat.add_comm] using h {a} (Finset.singleton_subset_iff.mpr ha)
end GraphUnion9840

namespace GraphClean9840
open GraphRows9840
abbrev R := Finset V
abbrev Group := Finset E
def onRow (r : Nat) (u : V) := (varWord u).getLsbD r
def Hits (X : R) (r : Nat) : Prop := ∃ u∈X, onRow r u=true
def N (c : V) := Finset.univ.filter fun u => adjacent c u
def star (c : V) (X : R) : Group :=
  Finset.univ.filter fun e : E => onRow e.val c = true ∧ ∃ u∈X, onRow e.val u=true

theorem star_mem {c X e} : e ∈ star c X ↔ onRow e.val c=true ∧ Hits X e.val := by
  simp [star,Hits]

theorem star_union (c : V) (X Y : R) : star c (X∪Y)=star c X ∪ star c Y := by
  ext e
  simp only [star_mem,Finset.mem_union,Hits]
  aesop

def negPart (v : V) : BitVec 685 := (varWord v).extractLsb' 95 685

theorem negPart_bit (v : V) (k : Fin 685) : (negPart v).getLsbD k.val = onRow (rneg k) v := by
  simp only [negPart,onRow,rneg,BitVec.getLsbD_extractLsb',k.isLt,decide_true,Bool.true_and]

set_option maxHeartbeats 4000000 in
theorem adjacent_certificate : ∀ u v : V,
    adjacent u v = true ↔ negPart u &&& negPart v = 0 := by decide +kernel

theorem adj_iff_neg (u v : V) :
    adjacent u v=true ↔ ∀ k : Fin 685, ¬ (onRow (rneg k) u=true ∧ onRow (rneg k) v=true) := by
  rw [adjacent_certificate,BitVec.eq_of_getLsbD_eq_iff]
  constructor
  · intro h k
    have hz := h k.val k.isLt
    intro ⟨hu,hv⟩
    rw [BitVec.getLsbD_and, negPart_bit u k, negPart_bit v k, hu, hv] at hz
    simp at hz
  · intro h i hi
    have hn := h ⟨i,hi⟩
    have bu := negPart_bit u ⟨i,hi⟩
    have bv := negPart_bit v ⟨i,hi⟩
    change (negPart u).getLsbD i = _ at bu
    change (negPart v).getLsbD i = _ at bv
    simp only [BitVec.getLsbD_and,bu,bv]
    cases hu : onRow (rneg ⟨i,hi⟩) u <;> cases hv : onRow (rneg ⟨i,hi⟩) v <;> simp_all

theorem adj_sym (u v : V) : adjacent u v=adjacent v u := by revert u v; decide +kernel

theorem neighbor_iff {c u : V} : u∈N c ↔ adjacent c u=true := by simp [N]

theorem unique_center {c d : V} {X : R} (large : 2≤X.card) (a : X ⊆ N c) (b : X ⊆ N d) : c=d := by
  by_contra ne
  obtain ⟨u,hu,v,hv,uv⟩ := Finset.one_lt_card.mp large
  have q := no_square c d u v ne uv (neighbor_iff.mp (a hu)) (neighbor_iff.mp (a hv))
      (neighbor_iff.mp (b hu))
  simp [neighbor_iff.mp (b hv)] at q

theorem thin_side {X Y : R}
    (safe : ∀ u∈X, ∀ v∈Y, adjacent u v=true) : X.card≤1 ∨ Y.card≤1 := by
  by_cases small : X.card≤1
  · exact Or.inl small
  · right
    by_contra! hy
    obtain ⟨u,hu,v,hv,uv⟩ := Finset.one_lt_card.mp (show 1<X.card by omega)
    obtain ⟨w,hw,z,hz,wz⟩ := Finset.one_lt_card.mp hy
    have q := no_square u v w z uv wz (safe _ hu _ hw) (safe _ hu _ hz) (safe _ hv _ hw)
    simp [safe _ hv _ hz] at q

set_option maxHeartbeats 4000000 in
theorem simple_star : ∀ c v : V, v∈N c → (star c {v}).card ≤ 1 := by
  decide +kernel

theorem star_small (c : V) (X : R) (sub : X⊆N c) (s : X.card≤1) : (star c X).card≤1 := by
  by_cases he : X=∅
  · subst X
    simp [star]
  · have hn := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr he)
    obtain ⟨v,hv⟩ := Finset.card_eq_one.mp (show X.card=1 by omega)
    subst X
    exact simple_star _ _ (sub (Finset.mem_singleton_self _))

def matched : Fin 20 → E := ![1, 5, 11, 16, 21, 25, 27, 34, 41, 45, 51, 55, 61, 66, 68, 71, 77, 80, 86, 90]
set_option maxHeartbeats 4000000 in
theorem disjoint_matching : ∀ i j : Fin 20, ∀ v : V,
    onRow (matched i).val v=true → onRow (matched j).val v=true → i=j := by decide +kernel
theorem matching_cover (X : R) (h : ∀ e : E, Hits X e.val) : 20≤X.card := by
  classical
  have representatives (i : Fin 20) : ∃ v : X, onRow (matched i).val v.val=true := by
    obtain ⟨v,hv,hon⟩ := h (matched i)
    exact ⟨⟨v,hv⟩,hon⟩
  choose f hf using representatives
  have inj : Function.Injective f := by
    intro i j eq
    exact disjoint_matching i j (f i).val (hf i) (eq.symm ▸ hf j)
  simpa using Fintype.card_le_of_injective _ inj

theorem raw_alive : ∀ v : V, ∃ r : Fin 685, onRow (rneg r) v=true := by decide +kernel
theorem target_pos : ∀ e : E, goal.getLsbD e.val=true := by decide +kernel
theorem target_neg : ∀ r : Fin 685, goal.getLsbD (rneg r)=false := by decide +kernel
end GraphClean9840

namespace GraphClean9840
open GraphRows9840 GraphUnion9840
structure Pool where
  rich : Family E
  light : Family V
  claimed : Family E

structure Budget (s : Pool) (r l t : Nat) : Prop where
  richCost : cap s.rich r
  lightCost : cap s.light l
  claimCost : s.claimed.card ≤ t
  covers : s.claimed ⊆ s.rich
  richSmall : ∀ a : Group, a.card≤1 → a∈s.rich
  lightSmall : ∀ a : R, a.card≤1 → a∈s.light

structure Extends (s z : Pool) : Prop where
  rich : s.rich ⊆ z.rich
  light : s.light ⊆ z.light
  claimed : s.claimed ⊆ z.claimed

def blocks (s : Pool) := s.claimed.biUnion id
def Dom (w : Word) (X : R) : Prop := ∀ e : E, w.getLsbD e.val=true → Hits X e.val
structure Wire (s : Pool) (w : Word) (X : R) : Prop where
  rawSound : ∀ r, Hits X r → w.getLsbD r=true
  origin : ∀ e : E, w.getLsbD e.val=true → Hits X e.val ∨ e∈blocks s
  group : ∀ c, X⊆N c → star c X∈s.rich
  cover : X.card≤1 → ∃ Y∈s.light, Dom w Y

def Ready (s : Pool) (w : Word) := ∃ X, Wire s w X
theorem widen {s z} (h : Extends s z) {w X} (hw : Wire s w X) : Wire z w X := by
  refine ⟨hw.rawSound,?_,fun c hc => h.rich (hw.group c hc),?_⟩
  · intro e yes
    rcases hw.origin e yes with hx|hb
    · exact Or.inl hx
    · obtain ⟨block,mem,hit⟩ := Finset.mem_biUnion.mp hb
      exact Or.inr (Finset.mem_biUnion.mpr ⟨_,h.claimed mem,hit⟩)
  · intro small
    obtain ⟨Y,hy,d⟩ := hw.cover small
    exact ⟨Y,h.light hy,d⟩

def units (α : Type) [Fintype α] [DecidableEq α] :=
  (Finset.univ : Finset α).powerset.filter fun t => t.card≤1
theorem in_units {α : Type} [Fintype α] [DecidableEq α] (x : Finset α) :
    x ∈ units α ↔ x.card≤1 := by simp [units]
def start : Pool := ⟨units E,units V,∅⟩
theorem startBudget : Budget start 0 0 0 := by
  exact ⟨small (fun _ h => (in_units _).mp h), small (fun _ h => (in_units _).mp h),
    by simp [start],Finset.empty_subset _, fun _ h => (in_units _).mpr h, fun _ h => (in_units _).mpr h⟩

theorem zero_wire {s r l t} (B : Budget s r l t) : Wire s 0 ∅ := by
  refine ⟨by simp [Hits], by simp, ?_,?_⟩
  · intro c sub
    exact B.richSmall _ (star_small _ _ sub (by simp))
  · intro _
    exact ⟨∅,B.lightSmall _ (by simp),by simp [Dom]⟩

theorem input_wire {s r l t} (B : Budget s r l t) (v : V) : Wire s (varWord v) {v} := by
  refine ⟨?_,?_,?_,?_⟩
  · simp [Hits,onRow]
  · intro e h
    exact Or.inl ⟨v,by simp,h⟩
  · intro c sub
    exact B.richSmall _ (star_small _ _ sub (by simp))
  · intro _
    exact ⟨{v},B.lightSmall _ (by simp),fun e h => ⟨v,by simp,h⟩⟩

theorem addRich {s r l t} (B : Budget s r l t) (x y : Group) (hx : x∈s.rich) (hy : y∈s.rich) :
    let z : Pool := {s with rich := insert (x∪y) s.rich}
    Extends s z ∧ Budget z (r+1) l t := by
  exact ⟨⟨Finset.subset_insert _ _,Finset.Subset.rfl,Finset.Subset.rfl⟩,
    merge B.richCost hx hy,B.lightCost,B.claimCost,B.covers.trans (Finset.subset_insert _ _),
    fun a h => Finset.mem_insert_of_mem (B.richSmall a h),B.lightSmall⟩

theorem addLight {s r l t} (B : Budget s r l t) (x y : R) (hx : x∈s.light) (hy : y∈s.light) :
    let z : Pool := {s with light := insert (x∪y) s.light}
    Extends s z ∧ Budget z r (l+1) t := by
  exact ⟨⟨Finset.Subset.rfl,Finset.subset_insert _ _,Finset.Subset.rfl⟩,
    B.richCost,merge B.lightCost hx hy,B.claimCost,B.covers,B.richSmall,
    fun a h => Finset.mem_insert_of_mem (B.lightSmall a h)⟩

theorem addBlock {s r l t} (B : Budget s r l t) (x : Group) (hx : x∈s.rich) :
    let z : Pool := {s with claimed := insert x s.claimed}
    Extends s z ∧ Budget z r l (t+1) := by
  exact ⟨⟨Finset.Subset.rfl,Finset.Subset.rfl,Finset.subset_insert _ _⟩,
    B.richCost,B.lightCost,(Finset.card_insert_le _ _).trans (by have := B.claimCost;omega),
    Finset.insert_subset hx B.covers,B.richSmall,B.lightSmall⟩
end GraphClean9840

namespace GraphClean9840
open GraphRows9840 GraphUnion9840

def Advance (s : Pool) (r l t : Nat) (w : Word) : Prop :=
  ∃ z r' l' t', Extends s z ∧ Budget z r' l' t' ∧ r'+l'+t'=r+l+t+1 ∧ Ready z w

theorem hits_union {X Y : R} {r : Nat} : Hits (X∪Y) r ↔ Hits X r ∨ Hits Y r := by
  simp only [Hits,Finset.mem_union]
  aesop

theorem or_wire {z : Pool} {a b : Word} {X Y : R} (ha : Wire z a X) (hb : Wire z b Y)
    (groups : ∀ c,X∪Y⊆N c → star c (X∪Y)∈z.rich)
    (light : (X∪Y).card≤1 → ∃ P∈z.light, Dom (a|||b) P) :
    Wire z (a|||b) (X∪Y) := by
  refine ⟨?_,?_,groups,light⟩
  · intro r h
    rcases hits_union.mp h with h|h
    · simp [ha.rawSound _ h]
    · simp [hb.rawSound _ h]
  · intro e h
    have split : a.getLsbD e.val=true ∨ b.getLsbD e.val=true := by simpa using h
    rcases split with yes|yes
    · exact (ha.origin _ yes).imp_left (fun v => hits_union.mpr (Or.inl v))
    · exact (hb.origin _ yes).imp_left (fun v => hits_union.mpr (Or.inr v))

theorem or_step {s r l t a b X Y} (B : Budget s r l t) (ha : Wire s a X) (hb : Wire s b Y) :
    Advance s r l t (a|||b) := by
  classical
  by_cases small : (X∪Y).card≤1
  · have sx := (Finset.card_le_card (Finset.subset_union_left (s₁:=X) (s₂:=Y))).trans small
    have sy := (Finset.card_le_card (Finset.subset_union_right (s₁:=X) (s₂:=Y))).trans small
    obtain ⟨P,hp,cp⟩ := ha.cover sx
    obtain ⟨Q,hq,cq⟩ := hb.cover sy
    let z : Pool := {s with light := insert (P∪Q) s.light}
    obtain ⟨ext,bud⟩ := addLight B _ _ hp hq
    refine ⟨z,r,l+1,t,ext,bud,by omega,X∪Y,or_wire (widen ext ha) (widen ext hb) ?_ ?_⟩
    · exact fun c sub => bud.richSmall _ (star_small c _ sub small)
    · intro _
      refine ⟨P∪Q,Finset.mem_insert_self _ _,?_⟩
      intro e h
      have split : a.getLsbD e.val=true ∨ b.getLsbD e.val=true := by simpa using h
      exact hits_union.mpr (split.imp (cp e) (cq e))
  · by_cases ok : ∃ c, X∪Y⊆N c
    · obtain ⟨c,hc⟩ := ok
      have hx := ha.group c (Finset.subset_union_left.trans hc)
      have hy := hb.group c (Finset.subset_union_right.trans hc)
      let z : Pool := {s with rich := insert (star c X ∪ star c Y) s.rich}
      obtain ⟨ext,bud⟩ := addRich B _ _ hx hy
      refine ⟨z,r+1,l,t,ext,bud,by omega,X∪Y,or_wire (widen ext ha) (widen ext hb) ?_ ?_⟩
      · intro d sub
        have eq := unique_center (X:=X∪Y) (by omega) sub hc
        subst d
        rw [star_union]
        exact Finset.mem_insert_self _ _
      · exact fun h => False.elim (small h)
    · have h0 := B.richSmall ∅ (by simp)
      obtain ⟨ext,bud⟩ := addRich B _ _ h0 h0
      refine ⟨_,r+1,l,t,ext,bud,by omega,X∪Y,or_wire (widen ext ha) (widen ext hb) ?_ ?_⟩
      · exact fun c hc => False.elim (ok ⟨c,hc⟩)
      · exact fun h => False.elim (small h)

def clean (w : Word) : Prop := ∀ k : Fin 685, w.getLsbD (rneg k)=false

theorem safe_raw {s a b X Y} (ha : Wire s a X) (hb : Wire s b Y) (safe : clean (a&&&b)) :
    ∀ u∈X, ∀ v∈Y, adjacent u v=true := by
  intro u hu v hv
  apply (adj_iff_neg _ _).mpr
  intro k both
  have h₁ := ha.rawSound _ ⟨u,hu,both.1⟩
  have h₂ := hb.rawSound _ ⟨v,hv,both.2⟩
  have no := safe k
  simp [h₁,h₂] at no

theorem rectangle_one {s : Pool} {b : Word} {X Y : R} {r l t}
    (B : Budget s r l t) (hb : Wire s b Y) (small : X.card≤1)
    (safe : ∀ u∈X, ∀ v∈Y, adjacent u v=true) :
    ∃ T∈s.rich, ∀ e : E, Hits X e.val → Hits Y e.val → e∈T := by
  by_cases emp : X=∅
  · subst X
    exact ⟨∅,B.richSmall _ (by simp),by simp [Hits]⟩
  · have pos := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr emp)
    obtain ⟨v,hv⟩ := Finset.card_eq_one.mp (show X.card=1 by omega)
    subst X
    have sub : Y ⊆ N v := fun u hu => neighbor_iff.mpr (safe _ (by simp) _ hu)
    refine ⟨_,hb.group v sub,?_⟩
    intro e vx vy
    exact star_mem.mpr ⟨by simpa [Hits] using vx,vy⟩

theorem and_step {s r l t a b X Y} (B : Budget s r l t) (ha : Wire s a X) (hb : Wire s b Y)
    (safe : clean (a&&&b)) : Advance s r l t (a&&&b) := by
  have paired := safe_raw ha hb safe
  have thin := thin_side paired
  have rectangle : ∃ T∈s.rich, ∀ e : E, Hits X e.val → Hits Y e.val → e∈T := by
    rcases thin with x|y
    · exact rectangle_one B hb x paired
    · have sym u (hu : u∈Y) v (hv : v∈X) : adjacent u v=true := by rw [adj_sym];exact paired _ hv _ hu
      obtain ⟨T,m,h⟩ := rectangle_one B ha y sym
      exact ⟨T,m,fun e hh gg => h e gg hh⟩
  obtain ⟨block,mem,rect⟩ := rectangle
  let z : Pool := {s with claimed := insert block s.claimed}
  obtain ⟨ext,bud⟩ := addBlock B block mem
  refine ⟨z,r,l,t+1,ext,bud,by omega,∅,?_,?_,?_,?_⟩
  · simp [Hits]
  · intro e yes
    have on : a.getLsbD e.val=true ∧ b.getLsbD e.val=true := by simpa using yes
    rcases (widen ext ha).origin e on.1 with ax|old
    · rcases (widen ext hb).origin e on.2 with byy|old
      · exact Or.inr (Finset.mem_biUnion.mpr ⟨block,Finset.mem_insert_self _ _,rect _ ax byy⟩)
      · exact Or.inr old
    · exact Or.inr old
  · exact fun c sub => bud.richSmall _ (star_small _ _ sub (by simp))
  · intro _
    rcases thin with sm|sm
    · obtain ⟨P,memP,dom⟩ := ha.cover sm
      exact ⟨P,memP,fun e h => dom e ((Bool.and_eq_true_iff.mp (by simpa only [BitVec.getLsbD_and] using h)).1)⟩
    · obtain ⟨P,memP,dom⟩ := hb.cover sm
      exact ⟨P,memP,fun e h => dom e ((Bool.and_eq_true_iff.mp (by simpa only [BitVec.getLsbD_and] using h)).2)⟩
end GraphClean9840


namespace GraphClean9840
open GraphRows9840 GraphUnion9840
theorem output_lower {s r l t} (B : Budget s r l t) (h : Ready s goal) : 114 ≤ r+l+t := by
  obtain ⟨X,w⟩ := h
  have emp : X=∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hv
    obtain ⟨k,hk⟩ := raw_alive v
    have yes := w.rawSound _ ⟨v,hv,hk⟩
    rw [target_neg k] at yes
    contradiction
  subst X
  have all : blocks s = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro e
    have v := w.origin e (target_pos e)
    simpa [Hits] using v
  obtain ⟨P,hP,dom⟩ := w.cover (by simp)
  have lb1 := matching_cover P (fun e => dom e (target_pos e))
  have lb2 := one B.lightCost hP
  have area := B.richCost s.claimed B.covers
  change (blocks s).card ≤ s.claimed.card+r at area
  rw [all] at area
  simp only [Finset.card_univ,Fintype.card_fin] at area
  have claimed := B.claimCost
  omega


end GraphClean9840

namespace GraphClean9840
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
open GraphRows9840 GraphUnion9840 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def ones : Word := BitVec.allOnes 780
@[local simp] theorem ones_or (w : Word) : ones ||| w = ones := BitVec.allOnes_or
@[local simp] theorem or_ones (w : Word) : w ||| ones = ones := BitVec.or_allOnes
@[local simp] theorem ones_and (w : Word) : ones &&& w = w := BitVec.allOnes_and
@[local simp] theorem and_ones (w : Word) : w &&& ones = w := BitVec.and_allOnes
def sparse (w : Word) : Prop := ∃ pivot : E, ∀ e : E, w.getLsbD e.val=true → e=pivot
def gateWord (g : Gate) (w : List Word) : Word :=
  let vs := g.inputs.map fun i => w.getD i 0
  match g.op with
  | .and => vs.foldr (· &&& ·) ones
  | .or => vs.foldr (· ||| ·) 0
  | _ => 0
def tick (w : List Word) (g : Gate) := w ++ [gateWord g w]

def permit (g : Gate) (w : List Word) : Prop :=
  ∀ i j, g.op = .and → g.inputs = [i,j] →
    let a := w.getD i 0
    let b := w.getD j 0
    a &&& b = a ∨ a &&& b = b ∨ sparse (a &&& b) ∨ clean (a &&& b)

def permitted (w : List Word) : List Gate → Prop
  | [] => True
  | g :: gs => permit g w ∧ permitted (tick w g) gs

def OK (s : Pool) (w : Word) : Prop := w = ones ∨ Ready s w
def UpTo (s : Pool) (r l t : Nat) (w : Word) : Prop :=
  ∃ z R L T, Extends s z ∧ Budget z R L T ∧ R+L+T ≤ r+l+t+1 ∧ OK z w

theorem keep {s r l t w} (B : Budget s r l t) (h : OK s w) : UpTo s r l t w :=
  ⟨s,r,l,t,⟨Finset.Subset.rfl,Finset.Subset.rfl,Finset.Subset.rfl⟩,B,by omega,h⟩

theorem spend {s r l t w} (h : Advance s r l t w) : UpTo s r l t w := by
  obtain ⟨z,R,L,T,ext,B,eq,ok⟩ := h
  exact ⟨z,R,L,T,ext,B,by omega,Or.inr ok⟩

theorem up_or {s r l t a b} (B : Budget s r l t) (ha : OK s a) (hb : OK s b) :
    UpTo s r l t (a ||| b) := by
  rcases ha with rfl|⟨X,hX⟩
  · apply keep B (Or.inl _)
    simp
  rcases hb with rfl|⟨Y,hY⟩
  · apply keep B (Or.inl _)
    simp
  exact spend (or_step B hX hY)

theorem has_end : ∀ e : E, ∃ v : V, onRow e.val v = true := by decide +kernel
theorem up_sparse {s r l t w} (B : Budget s r l t) (few : sparse w) : UpTo s r l t w := by
  obtain ⟨e,only⟩ := few
  obtain ⟨v,hv⟩ := has_end e
  let z : Pool := {s with claimed := insert {e} s.claimed}
  obtain ⟨ext,bud⟩ := addBlock B {e} (B.richSmall _ (by simp))
  refine ⟨z,r,l,t+1,ext,bud,by omega,Or.inr ⟨∅,?_,?_,?_,?_⟩⟩
  · simp [Hits]
  · intro j h
    have eq := only j h
    subst j
    exact Or.inr (Finset.mem_biUnion.mpr ⟨{e},Finset.mem_insert_self _ _,by simp⟩)
  · intro c sub
    exact bud.richSmall _ (star_small c _ sub (by simp))
  · intro _
    refine ⟨{v},bud.lightSmall _ (by simp),?_⟩
    intro j h
    exact ⟨v,by simp,only j h ▸ hv⟩

theorem up_and {s r l t a b} (B : Budget s r l t) (ha : OK s a) (hb : OK s b)
    (good : a &&& b = a ∨ a &&& b = b ∨ sparse (a &&& b) ∨ clean (a &&& b)) : UpTo s r l t (a &&& b) := by
  rcases good with same|same|few|cleaned
  · rw [same]; exact keep B ha
  · rw [same]; exact keep B hb
  · exact up_sparse B few
  rcases ha with rfl|⟨X,hX⟩
  · simpa using keep B hb
  rcases hb with rfl|⟨Y,hY⟩
  · simpa using keep B (show OK s a from Or.inr ⟨X,hX⟩)
  exact spend (and_step B hX hY cleaned)

theorem allowed_tick {s r l t} (B : Budget s r l t) (w : List Word)
    (old : ∀ x ∈ w, OK s x) (g : Gate) (hop : g.op = .and ∨ g.op = .or)
    (hlen : g.inputs.length ≤ 2) (p : permit g w) : UpTo s r l t (gateWord g w) := by
  have lookup (i : Nat) : OK s (w.getD i 0) := by
    by_cases h : i < w.length
    · rw [List.getD_eq_getElem _ _ h]; exact old _ (List.getElem_mem h)
    · rw [List.getD_eq_default _ _ (by omega)]; exact Or.inr ⟨_,zero_wire B⟩
  rcases eq : g.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · rcases hop with h|h
    · simpa [gateWord,h,eq] using keep B (show OK s ones from Or.inl rfl)
    · simpa [gateWord,h,eq] using keep B (show OK s 0 from Or.inr ⟨_,zero_wire B⟩)
  · rcases hop with h|h <;> simpa [gateWord,h,eq] using keep B (lookup a)
  · rcases hop with h|h
    · simpa [gateWord,h,eq] using up_and B (lookup a) (lookup b) (p a b h eq)
    · simpa [gateWord,h,eq] using up_or B (lookup a) (lookup b)
  · simp [eq] at hlen

theorem word_program (gs : List Gate) (w : List Word) {s r l t} (B : Budget s r l t)
    (ops : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    (old : ∀ x ∈ w, OK s x) (p : permitted w gs) :
    ∃ z R L T, Budget z R L T ∧ R+L+T ≤ r+l+t+gs.length ∧ ∀ x ∈ gs.foldl tick w, OK z x := by
  induction gs generalizing w s r l t with
  | nil => exact ⟨s,r,l,t,B,by simp,old⟩
  | cons g gs ih =>
    have hg := ops g List.mem_cons_self
    obtain ⟨m,r',l',t',ext,bud,cost,new⟩ := allowed_tick B w old g hg.1 hg.2 p.1
    have next : ∀ x ∈ tick w g, OK m x := by
      intro x hx
      rcases List.mem_append.mp hx with prior|last
      · rcases old x prior with h|⟨X,hX⟩
        · exact Or.inl h
        · exact Or.inr ⟨X,widen ext hX⟩
      · exact List.mem_singleton.mp last ▸ new
    obtain ⟨z,R,L,T,Bz,sz,endok⟩ := ih _ bud (fun g' hg' => ops g' (List.mem_cons_of_mem _ hg')) next p.2
    exact ⟨z,R,L,T,Bz,by simp only [List.length_cons];omega,endok⟩

theorem word_lower (C : Circuit) (hm : Monotone2 C) (h : permitted words C.gates)
    (hit : (C.gates.foldl tick words).getD C.output 0 = goal) : 114 ≤ C.size := by
  obtain ⟨s,r,l,t,B,sz,ready⟩ := word_program C.gates words startBudget
    (fun g hg => by simpa using hm g hg) (by
      intro x hx
      obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hx
      have len : words.length=40 := rfl
      let j : V := ⟨i.val, by rw [←len]; exact i.isLt⟩
      exact Or.inr ⟨_, by simpa [varWord,j,List.getD_eq_getElem?_getD,i.isLt] using input_wire startBudget j⟩) h
  have meet : goal ∈ C.gates.foldl tick words := by
    by_cases hi : C.output < (C.gates.foldl tick words).length
    · rw [List.getD_eq_getElem _ _ hi] at hit
      exact hit ▸ List.getElem_mem hi
    · rw [List.getD_eq_default _ _ (by omega)] at hit
      exact False.elim ((by decide : (0 : Word) ≠ goal) hit)
  rcases ready goal meet with eq|ok
  · exact False.elim ((by decide : goal ≠ ones) eq)
  have bound := output_lower B ok
  change 114 ≤ C.gates.length
  omega
end GraphClean9840

namespace GraphClean9840
open GraphRows9840 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def bitAt (k : Nat) (a : Word) := a.getLsbD k
theorem map_lookup (k i : Nat) (w : List Word) :
    (w.map (bitAt k)).getD i false = bitAt k (w.getD i 0) := by
  by_cases h : i<w.length <;> simp [List.getD_eq_getElem?_getD,h,bitAt]

theorem read_and (k : Fin 780) (xs : List Word) :
    bitAt k.val (xs.foldr (· &&& ·) ones) = (xs.map (bitAt k.val)).all id := by
  induction xs with
  | nil => exact (BitVec.getLsbD_allOnes.trans (decide_eq_true k.isLt))
  | cons a xs ih => simp [bitAt] at ih ⊢; rw [ih]

theorem read_or (k : Fin 780) (xs : List Word) :
    bitAt k.val (xs.foldr (· ||| ·) 0) = (xs.map (bitAt k.val)).any id := by
  induction xs with
  | nil => simp [bitAt]
  | cons a xs ih => simp [bitAt] at ih ⊢; rw [ih]

theorem eval_step (k : Fin 780) (g : Gate) (w : List Word) (h : g.op = .and ∨ g.op = .or) :
    bitAt k.val (gateWord g w) = g.op.eval (g.inputs.map fun i => (w.map (bitAt k.val)).getD i false) := by
  rcases h with h|h
  · simp only [gateWord,h,read_and,GateOp.eval,List.map_map,Function.comp_def,map_lookup]
  · simp only [gateWord,h,read_or,GateOp.eval,List.map_map,Function.comp_def,map_lookup]

theorem rows_run (k : Fin 780) (gs : List Gate) (w : List Word)
    (hm : ∀ g ∈ gs, g.op = .and ∨ g.op = .or) :
    (gs.foldl tick w).map (bitAt k.val) =
      gs.foldl (fun xs g => xs ++ [g.op.eval (g.inputs.map fun i => xs.getD i false)]) (w.map (bitAt k.val)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (tick w g) (fun g' hg' => hm g' (List.mem_cons_of_mem _ hg'))]
    rw [tick,List.map_append,List.map_singleton,eval_step k g w (hm g List.mem_cons_self)]

theorem word_output (C : Circuit) (hm : Monotone2 C) (k : Fin 780) :
    bitAt k.val ((C.gates.foldl tick words).getD C.output 0) = C.eval (words.map (bitAt k.val)) := by
  rw [← map_lookup,rows_run k C.gates words (fun g hg => by simpa using (hm g hg).1)]
  rfl

def target (x : Fin 40 → Bool) := Simlowker.Graph9840.target x = true
def correct (C : Circuit) := ∀ x : Fin 40 → Bool,C.eval (List.ofFn x)=true ↔ target x
def input (r : Nat) (i : Fin 40) := bitAt r (varWord i)
theorem row_table (r : Nat) : words.map (bitAt r) = List.ofFn (input r) := by
  apply List.ext_getElem
  · rw [List.length_map,List.length_ofFn]; rfl
  · intro i hi _
    have h : i<words.length := by simpa using hi
    simp only [List.getElem_map,List.getElem_ofFn,input,varWord,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem h,Option.getD_some]
theorem row_yes : ∀ e : E, target (input e.val) := by unfold target; decide +kernel
set_option maxHeartbeats 0 in
theorem row_no : ∀ j : Fin 685, ¬target (input (rneg j)) := by unfold target;decide +kernel
theorem actual_lower (C : Circuit) (hm : Monotone2 C) (hc : correct C) (p : permitted words C.gates) :
    114 ≤ C.size := by
  apply word_lower C hm p
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i hi
  change bitAt i _ = _
  rw [word_output C hm ⟨i,hi⟩,row_table]
  by_cases he : i<95
  · exact ((hc _).2 (row_yes ⟨i,he⟩)).trans (target_pos ⟨i,he⟩).symm
  · let j : Fin 685 := ⟨i-95,by omega⟩
    have eq : rneg j=i := by simp [rneg,j];omega
    change C.eval (List.ofFn (input i))=goal.getLsbD i
    rw [← eq,target_neg]
    cases h : C.eval (List.ofFn (input (rneg j))) with
    | false => rfl
    | true => exact (row_no j ((hc _).1 h)).elim
end GraphClean9840

namespace GraphFormula9840
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 65536
set_option maxHeartbeats 0
inductive Formula where
  | var (i : Fin 42)
  | disj (l r : Formula)
  | conj (l r : Formula)

def Formula.eval (v : Fin 42 → Bool) : Formula → Bool
  | .var i => v i
  | .disj l r => l.eval v || r.eval v
  | .conj l r => l.eval v && r.eval v

def Formula.leaves : Formula → Nat
  | .var _ => 1
  | .conj a b | .disj a b => a.leaves+b.leaves

def base (x : Fin 40 → Bool) (i : Fin 42) := if h : i.val<40 then x ⟨i.val,h⟩ else decide (i.val=41)
def init : List Formula := List.ofFn fun i : Fin 40 => Formula.var ⟨i.val,by omega⟩
def readF (ws : List Formula) (j : Nat) := ws.getD j (.var 40)
def two (f : Formula → Formula → Formula) (k : Fin 42) (ws : List Formula) : List Nat → Formula
  | [] => .var k
  | [a] => readF ws a
  | a::b::_ => f (readF ws a) (readF ws b)
def gateF (ws : List Formula) (g : Gate) : Formula :=
  match g.op with
  | .and => two .conj 41 ws g.inputs
  | .or => two .disj 40 ws g.inputs
  | _ => .var 40
def stepF (ws : List Formula) (g : Gate) := ws++[gateF ws g]
def expand (c : Circuit) := readF (c.gates.foldl stepF init) c.output
def realStep (xs : List Bool) (g : Gate) := xs++[g.op.eval (g.inputs.map fun i => xs.getD i false)]
theorem read_eval (x : Fin 40 → Bool) (ws : List Formula) (j : Nat) :
    (readF ws j).eval (base x)=(ws.map (fun f => f.eval (base x))).getD j false := by
  simp only [readF,List.getD_eq_getElem?_getD,List.getElem?_map]
  cases ws[j]? <;> rfl
theorem gate_eval (x : Fin 40 → Bool) (ws : List Formula) (g : Gate)
    (h : (g.op=.and ∨ g.op=.or) ∧ g.inputs.length ≤ 2) :
    (gateF ws g).eval (base x)=g.op.eval (g.inputs.map fun i => (ws.map (fun f => f.eval (base x))).getD i false) := by
  rcases g with ⟨op,ls⟩
  rcases h with ⟨hp,hl⟩
  change op=.and ∨ op=.or at hp
  change ls.length≤2 at hl
  rcases hp with rfl|rfl <;> rcases ls with _|⟨a,_|⟨b,_|⟨c,rest⟩⟩⟩ <;>
    simp_all [gateF,two,Formula.eval,base,GateOp.eval,read_eval]
theorem fold_eval (x : Fin 40 → Bool) (gs : List Gate)
    (h : ∀ g ∈ gs, (g.op=.and ∨ g.op=.or) ∧ g.inputs.length ≤ 2) (ws : List Formula) :
    (gs.foldl stepF ws).map (fun f => f.eval (base x))=gs.foldl realStep (ws.map (fun f => f.eval (base x))) := by
  induction gs generalizing ws with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons,List.foldl_cons, ih (fun a ha => h a (List.mem_cons_of_mem _ ha))]
    simp [stepF,realStep,gate_eval x ws g (h g List.mem_cons_self)]
theorem expand_eval (C : Circuit) (hm : Monotone2 C) (x : Fin 40 → Bool) :
    (expand C).eval (base x) = C.eval (List.ofFn x) := by
  rw [expand,read_eval,fold_eval _ _ (fun g hg => hm g hg)]
  have eq : init.map (fun f => f.eval (base x))=List.ofFn x := by
    rw [init,← List.ofFn_comp']
    rfl
  rw [eq]
  rfl
def starCircuit : Circuit := ⟨[⟨.or,[27,37]⟩,⟨.or,[25,40]⟩,⟨.or,[20,41]⟩,⟨.and,[0,42]⟩,⟨.or,[28,38]⟩,⟨.or,[26,44]⟩,⟨.or,[21,45]⟩,⟨.and,[1,46]⟩,⟨.or,[29,39]⟩,⟨.or,[27,48]⟩,⟨.or,[22,49]⟩,⟨.or,[21,50]⟩,⟨.and,[2,51]⟩,⟨.or,[28,30]⟩,⟨.or,[23,53]⟩,⟨.or,[22,54]⟩,⟨.or,[20,55]⟩,⟨.and,[3,56]⟩,⟨.or,[29,31]⟩,⟨.or,[24,58]⟩,⟨.or,[23,59]⟩,⟨.and,[4,60]⟩,⟨.or,[30,32]⟩,⟨.or,[25,62]⟩,⟨.or,[24,63]⟩,⟨.or,[21,64]⟩,⟨.and,[5,65]⟩,⟨.or,[31,33]⟩,⟨.or,[26,67]⟩,⟨.or,[25,68]⟩,⟨.or,[22,69]⟩,⟨.and,[6,70]⟩,⟨.or,[32,34]⟩,⟨.or,[27,72]⟩,⟨.or,[26,73]⟩,⟨.or,[23,74]⟩,⟨.and,[7,75]⟩,⟨.or,[33,35]⟩,⟨.or,[28,77]⟩,⟨.or,[27,78]⟩,⟨.or,[24,79]⟩,⟨.and,[8,80]⟩,⟨.or,[34,36]⟩,⟨.or,[29,82]⟩,⟨.or,[28,83]⟩,⟨.or,[25,84]⟩,⟨.and,[9,85]⟩,⟨.or,[35,37]⟩,⟨.or,[30,87]⟩,⟨.or,[29,88]⟩,⟨.or,[26,89]⟩,⟨.and,[10,90]⟩,⟨.or,[36,38]⟩,⟨.or,[31,92]⟩,⟨.or,[30,93]⟩,⟨.or,[27,94]⟩,⟨.and,[11,95]⟩,⟨.or,[37,39]⟩,⟨.or,[32,97]⟩,⟨.or,[31,98]⟩,⟨.or,[28,99]⟩,⟨.and,[12,100]⟩,⟨.or,[33,38]⟩,⟨.or,[32,102]⟩,⟨.or,[29,103]⟩,⟨.or,[20,104]⟩,⟨.and,[13,105]⟩,⟨.or,[34,39]⟩,⟨.or,[33,107]⟩,⟨.or,[30,108]⟩,⟨.and,[14,109]⟩,⟨.or,[34,35]⟩,⟨.or,[31,111]⟩,⟨.or,[21,112]⟩,⟨.or,[20,113]⟩,⟨.and,[15,114]⟩,⟨.or,[35,36]⟩,⟨.or,[32,116]⟩,⟨.or,[22,117]⟩,⟨.and,[16,118]⟩,⟨.or,[36,37]⟩,⟨.or,[33,120]⟩,⟨.or,[23,121]⟩,⟨.or,[21,122]⟩,⟨.and,[17,123]⟩,⟨.or,[37,38]⟩,⟨.or,[34,125]⟩,⟨.or,[24,126]⟩,⟨.or,[22,127]⟩,⟨.and,[18,128]⟩,⟨.or,[38,39]⟩,⟨.or,[35,130]⟩,⟨.or,[25,131]⟩,⟨.or,[23,132]⟩,⟨.and,[19,133]⟩,⟨.or,[129,134]⟩,⟨.or,[124,135]⟩,⟨.or,[119,136]⟩,⟨.or,[115,137]⟩,⟨.or,[110,138]⟩,⟨.or,[106,139]⟩,⟨.or,[101,140]⟩,⟨.or,[96,141]⟩,⟨.or,[91,142]⟩,⟨.or,[86,143]⟩,⟨.or,[81,144]⟩,⟨.or,[76,145]⟩,⟨.or,[71,146]⟩,⟨.or,[66,147]⟩,⟨.or,[61,148]⟩,⟨.or,[57,149]⟩,⟨.or,[52,150]⟩,⟨.or,[47,151]⟩,⟨.or,[43,152]⟩],153⟩
def starTree : Formula := (.disj ((.conj (.var 0) ((.disj (.var 20) ((.disj (.var 25) ((.disj (.var 27) (.var 37))))))))) ((.disj ((.conj (.var 1) ((.disj (.var 21) ((.disj (.var 26) ((.disj (.var 28) (.var 38))))))))) ((.disj ((.conj (.var 2) ((.disj (.var 21) ((.disj (.var 22) ((.disj (.var 27) ((.disj (.var 29) (.var 39))))))))))) ((.disj ((.conj (.var 3) ((.disj (.var 20) ((.disj (.var 22) ((.disj (.var 23) ((.disj (.var 28) (.var 30))))))))))) ((.disj ((.conj (.var 4) ((.disj (.var 23) ((.disj (.var 24) ((.disj (.var 29) (.var 31))))))))) ((.disj ((.conj (.var 5) ((.disj (.var 21) ((.disj (.var 24) ((.disj (.var 25) ((.disj (.var 30) (.var 32))))))))))) ((.disj ((.conj (.var 6) ((.disj (.var 22) ((.disj (.var 25) ((.disj (.var 26) ((.disj (.var 31) (.var 33))))))))))) ((.disj ((.conj (.var 7) ((.disj (.var 23) ((.disj (.var 26) ((.disj (.var 27) ((.disj (.var 32) (.var 34))))))))))) ((.disj ((.conj (.var 8) ((.disj (.var 24) ((.disj (.var 27) ((.disj (.var 28) ((.disj (.var 33) (.var 35))))))))))) ((.disj ((.conj (.var 9) ((.disj (.var 25) ((.disj (.var 28) ((.disj (.var 29) ((.disj (.var 34) (.var 36))))))))))) ((.disj ((.conj (.var 10) ((.disj (.var 26) ((.disj (.var 29) ((.disj (.var 30) ((.disj (.var 35) (.var 37))))))))))) ((.disj ((.conj (.var 11) ((.disj (.var 27) ((.disj (.var 30) ((.disj (.var 31) ((.disj (.var 36) (.var 38))))))))))) ((.disj ((.conj (.var 12) ((.disj (.var 28) ((.disj (.var 31) ((.disj (.var 32) ((.disj (.var 37) (.var 39))))))))))) ((.disj ((.conj (.var 13) ((.disj (.var 20) ((.disj (.var 29) ((.disj (.var 32) ((.disj (.var 33) (.var 38))))))))))) ((.disj ((.conj (.var 14) ((.disj (.var 30) ((.disj (.var 33) ((.disj (.var 34) (.var 39))))))))) ((.disj ((.conj (.var 15) ((.disj (.var 20) ((.disj (.var 21) ((.disj (.var 31) ((.disj (.var 34) (.var 35))))))))))) ((.disj ((.conj (.var 16) ((.disj (.var 22) ((.disj (.var 32) ((.disj (.var 35) (.var 36))))))))) ((.disj ((.conj (.var 17) ((.disj (.var 21) ((.disj (.var 23) ((.disj (.var 33) ((.disj (.var 36) (.var 37))))))))))) ((.disj ((.conj (.var 18) ((.disj (.var 22) ((.disj (.var 24) ((.disj (.var 34) ((.disj (.var 37) (.var 38))))))))))) ((.conj (.var 19) ((.disj (.var 23) ((.disj (.var 25) ((.disj (.var 35) ((.disj (.var 38) (.var 39))))))))))))))))))))))))))))))))))))))))))))))))
def valid (g : Gate) : Bool :=
  match g.op with
  | .and | .or => decide (g.inputs.length≤2)
  | _ => false
theorem star_mono : Monotone2 starCircuit := by
  have h : starCircuit.gates.all valid=true := by decide +kernel
  intro g hg
  have p := List.all_eq_true.mp h g hg
  cases e : g.op <;> simp_all [valid]
theorem star_size : starCircuit.size = 114 := rfl
theorem star_expands : expand starCircuit = starTree := by rfl
theorem star_eval (x : Fin 40 → Bool) : starTree.eval (base x)=Simlowker.Graph9840.target x := by
  simp [starTree, Formula.eval, base, Simlowker.Graph9840.target, Bool.and_or_distrib_left, Bool.or_assoc]
theorem star_correct : GraphClean9840.correct starCircuit := by
  intro x
  rw [← expand_eval _ star_mono,star_expands,star_eval]
  rfl
theorem unrestricted_upper : HasCircuitSize 40 Simlowker.Graph9840.target 114 := by
  refine ⟨starCircuit,?_,by decide,?_⟩
  · intro g hg
    obtain ⟨ops,arity⟩ := star_mono g hg
    exact ⟨ops.elim Or.inl (fun h => Or.inr (Or.inl h)),arity⟩
  · intro x
    exact Bool.eq_iff_iff.mpr (star_correct x)
#print axioms unrestricted_upper
end GraphFormula9840

namespace GraphFormula9840
open GraphRows9840 GraphClean9840 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def cleanCheck (w : Word) : Bool := (List.finRange 685).all fun k => !(w.getLsbD (rneg k))
def gateCheck (w : List Word) (g : Gate) : Bool :=
  match g.op with
  | .and => cleanCheck (gateWord g w)
  | _ => true
def starCheck (w : List Word) : List Gate → Bool
  | [] => true
  | g::gs => gateCheck w g && starCheck (tick w g) gs

theorem check_sound (w : List Word) (gs : List Gate) (checked : starCheck w gs=true) : permitted w gs := by
  induction gs generalizing w with
  | nil => trivial
  | cons g gs ih =>
    obtain ⟨hc,tail⟩ := Bool.and_eq_true_iff.mp checked
    refine ⟨?_,ih (tick w g) tail⟩
    intro i j op ins
    apply Or.inr;apply Or.inr;apply Or.inr
    have cc : cleanCheck (gateWord g w)=true := by simpa [gateCheck,op] using hc
    have ww : gateWord g w=w.getD i 0 &&& w.getD j 0 := by simp [gateWord,op,ins,GraphClean9840.and_ones]
    rw [←ww]
    intro k
    simpa using List.all_eq_true.mp cc k (List.mem_finRange k)

theorem optimum_in_class : permitted words starCircuit.gates ∧ starCircuit.size=114 ∧ correct starCircuit ∧
    ∀ C, Monotone2 C → correct C → permitted words C.gates → 114≤C.size := by
  exact ⟨check_sound _ _ (by decide +kernel),star_size,star_correct,actual_lower⟩

theorem star_leaves : starTree.leaves=115 := by decide +kernel
#print axioms optimum_in_class
end GraphFormula9840

namespace GraphClean9840
open GraphRows9840 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def obstruction (g : Gate) (w : List Word) : Prop :=
  ∃ i j, g.op = .and ∧ g.inputs = [i,j] ∧
    let a := w.getD i 0
    let b := w.getD j 0
    let v := a &&& b
    v ≠ a ∧ v ≠ b ∧
    (∃ e f : E, e ≠ f ∧ v.getLsbD e.val=true ∧ v.getLsbD f.val=true) ∧
    ∃ k : Fin 685, v.getLsbD (rneg k)=true

theorem obstruct {g : Gate} {w : List Word} (h : ¬ permit g w) : obstruction g w := by
  unfold permit at h
  dsimp only at h
  push Not at h
  obtain ⟨i,j,op,ins,na,nb,np,nc⟩ := h
  let v := w.getD i 0 &&& w.getD j 0
  change ¬ sparse v at np
  change ¬ clean v at nc
  unfold sparse at np
  push Not at np
  obtain ⟨e,he,_⟩ := np 0
  obtain ⟨f,hf,ne⟩ := np e
  unfold clean at nc
  push Not at nc
  obtain ⟨k,hk⟩ := nc
  have yes : v.getLsbD (rneg k)=true := by simpa using hk
  exact ⟨i,j,op,ins,na,nb,⟨e,f,Ne.symm ne,he,hf⟩,k,yes⟩

theorem locate (gs : List Gate) (w : List Word) (h : ¬ permitted w gs) :
    ∃ pre g post, gs = pre ++ g :: post ∧ obstruction g (pre.foldl tick w) := by
  induction gs generalizing w with
  | nil => exact False.elim (h trivial)
  | cons g gs ih =>
    by_cases head : permit g w
    · obtain ⟨pre,found,post,eq,bad⟩ := ih (tick w g) (fun htail => h ⟨head,htail⟩)
      exact ⟨g::pre,found,post,by simp [eq],bad⟩
    · exact ⟨[],g,gs,rfl,obstruct head⟩

theorem obstruction_required (C : Circuit) (hm : Monotone2 C) (small : C.size ≤ 113)
    (hc : correct C) : ∃ pre g post,C.gates=pre++g::post ∧ obstruction g (pre.foldl tick words) := by
  exact locate _ _ (fun hp => by have := actual_lower C hm hc hp;omega)
#print axioms obstruction_required
end GraphClean9840

namespace GraphClean9840.Trace
open GraphRows9840 GraphUnion9840 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
def reads (g : Gate) (m : List Bool) := ∃ i ∈ g.inputs, m.getD i false=true
abbrev St := List Word × List Bool
noncomputable def flag (s : St) (g : Gate) : Bool := by
  classical
  exact decide ((reads g s.2 ∨ ¬permit g s.1) ∧ ¬clean (gateWord g s.1))
noncomputable def step (s : St) (g : Gate) : St := (tick s.1 g,s.2++[flag s g])
def sink (s : St) (g : Gate) := g.op=.and ∧ reads g s.2 ∧ clean (gateWord g s.1) ∧ gateWord g s.1 ≠ 0
def sync (s : St) (v : List Word) := s.1.length=v.length ∧ s.2.length=v.length ∧
  ∀ i, (s.2.getD i false=false → s.1.getD i 0=v.getD i 0) ∧
    (s.2.getD i false=true → ¬clean (s.1.getD i 0))
theorem other {α : Type} (L : List α) (z d : α) (j : Nat) (h : j≠L.length) :
    (L++[z]).getD j d=L.getD j d := by
  by_cases hj : j<L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega),List.getD_eq_default _ _ (by omega)]
theorem last_get {α : Type} (xs : List α) (x d : α) : (xs++[x]).getD xs.length d=x := by simp
theorem extend {s : St} {v : List Word} {g a : Gate} (h : sync s v)
    (clear : flag s g=false → gateWord g s.1=gateWord a v) : sync (step s g) (tick v a) := by
  obtain ⟨hl,hm,h⟩ := h
  refine ⟨by simp [step,tick,hl],by simp [step,tick,hm],?_⟩
  intro i
  by_cases eq : i=v.length
  · subst i
    simp only [step,tick]
    rw [← hm,last_get,hm,← hl,last_get,hl,last_get]
    refine ⟨clear,?_⟩
    simp [flag]
  · simp only [step,tick,other _ _ _ _ eq,other _ _ _ _ (show i≠s.2.length by omega),
      other _ _ _ _ (show i≠s.1.length by omega)]
    exact h i

theorem equal_lookup {s : St} {v : List Word} {g : Gate} (h : sync s v) (no : ¬reads g s.2)
    {i : Nat} (hi : i ∈ g.inputs) : s.1.getD i 0 = v.getD i 0 := by
  apply (h.2.2 i).1
  cases e : s.2.getD i false with
  | false => rfl
  | true => exact (no ⟨i,hi,e⟩).elim

theorem equal_words {s : St} {v : List Word} {g : Gate} (h : sync s v) (no : ¬reads g s.2) :
    gateWord g s.1=gateWord g v := by
  have eq : g.inputs.map (fun i => s.1.getD i 0)=g.inputs.map (fun i => v.getD i 0) :=
    List.map_congr_left (fun i hi => equal_lookup h no hi)
  unfold gateWord
  rw [eq]

theorem equal_permit {s : St} {v : List Word} {g : Gate} (h : sync s v) (no : ¬reads g s.2)
    (p : permit g s.1) : permit g v := by
  intro i j op ins
  have ha := equal_lookup h no (i:=i) (by simp [ins])
  have hb := equal_lookup h no (i:=j) (by simp [ins])
  simpa only [ha,hb] using p i j op ins

theorem or_dirty {s : St} {v : List Word} {g : Gate} (h : sync s v) (yes : reads g s.2)
    (op : g.op=.or) : ¬clean (gateWord g s.1) := by
  obtain ⟨i,hi,flagged⟩ := yes
  have hh := (h.2.2 i).2 flagged
  unfold clean at hh
  push Not at hh
  obtain ⟨k,hk⟩ := hh
  have read : bitAt (rneg k) (gateWord g s.1)=true := by
    rw [eval_step ⟨rneg k,by simp [rneg];omega⟩ _ _ (Or.inr op)]
    simp only [op,GateOp.eval,List.any_map,List.any_eq_true,Function.comp_def,id_eq]
    refine ⟨i,hi,?_⟩
    rw [map_lookup]
    simpa only [bitAt, Bool.not_eq_false] using hk
  intro cl
  exact Bool.noConfusion (read.symm.trans (cl k))

theorem bad_dirty {g : Gate} {w : List Word} (p : ¬permit g w) : ¬clean (gateWord g w) := by
  obtain ⟨i,j,h,eq,_,_,_,k,hk⟩ := obstruct p
  intro cl
  have ww : gateWord g w = w.getD i 0 &&& w.getD j 0 := by simp [gateWord,h,eq,GraphClean9840.and_ones]
  exact Bool.noConfusion (hk.symm.trans (ww ▸ cl k))
def legal (g : Gate) := (g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2

theorem simulate_gate {s : St} {v : List Word} {g : Gate}
    (h : sync s v) (l : legal g) (ns : ¬sink s g) :
    ∃ a, legal a ∧ permit a v ∧ sync (step s g) (tick v a) := by
  classical
  by_cases yes : reads g s.2
  · rcases l.1 with op|op
    · let a : Gate := ⟨.or,[]⟩
      refine ⟨a,by simp [legal,a],by simp [permit,a],extend h ?_⟩
      intro f
      have cl : clean (gateWord g s.1) := by simpa [flag,yes] using f
      have zero : gateWord g s.1=0 := by by_contra nz; exact ns ⟨op,yes,cl,nz⟩
      exact zero
    · refine ⟨g,l,by simp [permit,op],extend h ?_⟩
      simp [flag,yes,or_dirty h yes op]
  · by_cases p : permit g s.1
    · exact ⟨g,l,equal_permit h yes p,extend h (fun _ => equal_words h yes)⟩
    · let a : Gate := ⟨.or,[]⟩
      refine ⟨a,by simp [legal,a],by simp [permit,a],extend h ?_⟩
      simp [flag,p,bad_dirty p]

noncomputable def initial : St := (words,List.replicate words.length false)
theorem start_sync : sync initial words := by
  refine ⟨rfl,by simp [initial],?_⟩
  intro i
  by_cases h : i<words.length <;>
    simp [initial,List.getD_eq_getElem?_getD,h]

theorem no_sink_sim (gs : List Gate) (s : St) (v : List Word)
    (l : ∀ g ∈ gs, legal g) (h : sync s v)
    (ns : ∀ pre g post, gs=pre++g::post → ¬sink (pre.foldl step s) g) :
    ∃ t : List Gate, t.length=gs.length ∧ (∀ g ∈ t, legal g) ∧ permitted v t ∧
      sync (gs.foldl step s) (t.foldl tick v) := by
  induction gs generalizing s v with
  | nil => exact ⟨[],rfl,by simp,trivial,h⟩
  | cons g gs ih =>
    obtain ⟨a,la,pa,hs⟩ := simulate_gate h (l _ List.mem_cons_self) (ns [] g gs rfl)
    obtain ⟨t,size,lt,pt,sync'⟩ := ih (step s g) (tick v a) (fun z hz => l _ (List.mem_cons_of_mem _ hz)) hs
      (fun pre z post eq => ns (g::pre) z post (by simp [eq]))
    exact ⟨a::t,by simp [size],by simpa using And.intro la lt,⟨pa,pt⟩,sync'⟩

theorem original (gs : List Gate) (s : St) : (gs.foldl step s).1=gs.foldl tick s.1 := by
  induction gs generalizing s with
  | nil => rfl
  | cons g gs ih => exact ih (step s g)

theorem marked_filter_required (C : Circuit) (hm : Monotone2 C) (small : C.size ≤ 113)
    (hit : (C.gates.foldl tick words).getD C.output 0=goal) :
    ∃ pre g post,C.gates=pre++g::post ∧ sink (pre.foldl step initial) g := by
  classical
  by_contra! no
  obtain ⟨t,sz,lt,pt,hs⟩ := no_sink_sim C.gates initial words (fun g hg => by simpa [legal] using hm g hg)
    start_sync (fun pre g post hg => no pre g post hg)
  have orig : (C.gates.foldl step initial).1.getD C.output 0=goal := by rw [original];exact hit
  have clear : (C.gates.foldl step initial).2.getD C.output false=false := by
    cases hh : (C.gates.foldl step initial).2.getD C.output false with
    | false => rfl
    | true => exact False.elim ((hs.2.2 C.output).2 hh (orig ▸ target_neg))
  have eq := (hs.2.2 C.output).1 clear
  let D : Circuit := ⟨t,C.output⟩
  have mono : Monotone2 D := by intro g hg;simpa [legal] using lt g hg
  have low := word_lower D mono pt (eq.symm.trans orig)
  change t.length ≥ 114 at low
  change C.gates.length ≤ 113 at small
  omega
end GraphClean9840.Trace

namespace GraphClean9840.Trace
open GraphRows9840 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 10000
set_option maxHeartbeats 800000

/-- An actual wire path. The first gate is a strict mixed AND. Each subsequent
gate on the path reads its predecessor and still accepts some nonedge pair.
The keep constructor skips gates not traversed by this path. -/
inductive MixedPath : List Gate → Nat → Prop where
  | source {pre : List Gate} {g : Gate} (bad : obstruction g (pre.foldl tick words)) :
      MixedPath (pre++[g]) (40+pre.length)
  | follow {pre : List Gate} {g : Gate} {i : Nat} (prev : MixedPath pre i) (uses : i∈g.inputs)
      (dirty : ¬clean (gateWord g (pre.foldl tick words))) :
      MixedPath (pre++[g]) (40+pre.length)
  | keep {pre : List Gate} {i : Nat} (g : Gate) (prev : MixedPath pre i) : MixedPath (pre++[g]) i

theorem len_flags (gs : List Gate) (s : St) : (gs.foldl step s).2.length=s.2.length+gs.length := by
  induction gs generalizing s with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons,ih]
    simp [step,Nat.add_comm,Nat.add_left_comm]

theorem flag_path (gs : List Gate) (i : Nat) (flagged : (gs.foldl step initial).2.getD i false=true) :
    MixedPath gs i := by
  induction gs using List.reverseRecOn generalizing i with
  | nil =>
    change (List.replicate words.length false).getD i false=true at flagged
    by_cases lt : i<words.length
    · simp [List.getD_eq_getElem?_getD,lt] at flagged
    · simp [List.getD_eq_getElem?_getD,lt] at flagged
  | append_singleton pre g ih =>
    let s := pre.foldl step initial
    have ll : s.2.length = 40+pre.length := (len_flags pre initial).trans (by rw [show initial.2.length=40 by decide])
    change ((pre++[g]).foldl step initial).2.getD i false=true at flagged
    rw [List.foldl_append] at flagged
    change (s.2++[flag s g]).getD i false=true at flagged
    by_cases last : i=s.2.length
    · subst i
      rw [last_get] at flagged
      have h : (reads g s.2 ∨ ¬permit g s.1) ∧ ¬clean (gateWord g s.1) := by simpa [flag] using flagged
      have eq : s.1 = pre.foldl tick words := original pre initial
      rw [ll]
      rcases h.1 with used|bad
      · obtain ⟨j,hj,marked⟩ := used
        exact MixedPath.follow (ih j marked) hj (eq ▸ h.2)
      · exact MixedPath.source (obstruct (eq ▸ bad))
    · rw [other _ _ _ _ last] at flagged
      exact MixedPath.keep g (ih i flagged)

theorem flags_dirty (gs : List Gate) (s : St) (len : s.1.length=s.2.length)
    (inv : ∀ i, s.2.getD i false=true → ¬clean (s.1.getD i 0)) :
    ∀ i, (gs.foldl step s).2.getD i false=true → ¬clean ((gs.foldl step s).1.getD i 0) := by
  induction gs generalizing s with
  | nil => exact inv
  | cons g gs ih =>
    apply ih (step s g) (by simp [step,tick,len])
    intro j
    by_cases eq : j=s.2.length
    · subst j
      change (s.2++[flag s g]).getD s.2.length false=true → ¬clean ((s.1++[gateWord g s.1]).getD s.2.length 0)
      rw [last_get,←len,last_get]
      simp [flag]
    · simp only [step,tick,other _ _ _ _ eq,other _ _ _ _ (show j≠s.1.length by omega)]
      exact inv j
theorem flag_dirty (gs : List Gate) (i : Nat) (m : (gs.foldl step initial).2.getD i false=true) :
    ¬clean ((gs.foldl step initial).1.getD i 0) :=
  flags_dirty _ _ (by simp [initial]) (fun j => (start_sync.2.2 j).2) _ m

theorem correct_word (C : Circuit) (hm : Monotone2 C) (hc : correct C) :
    (C.gates.foldl tick words).getD C.output 0=goal := by
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i hi
  change bitAt i _ = _
  rw [word_output C hm ⟨i,hi⟩,row_table]
  by_cases he : i<95
  · exact ((hc _).2 (row_yes ⟨i,he⟩)).trans (target_pos ⟨i,he⟩).symm
  · let j : Fin 685 := ⟨i-95,by omega⟩
    have eq : rneg j=i := by simp [rneg,j];omega
    change C.eval (List.ofFn (input i))=goal.getLsbD i
    rw [← eq,target_neg]
    cases h : C.eval (List.ofFn (input (rneg j))) with
    | false => rfl
    | true => exact (row_no j ((hc _).1 h)).elim

theorem positive_of_clean {v : Word} (cl : clean v) (nz : v≠0) : ∃ e : E, v.getLsbD e.val=true := by
  by_contra! none
  apply nz
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i hi
  by_cases pos : i<95
  · simpa using none ⟨i,pos⟩
  · let k : Fin 685 := ⟨i-95,by omega⟩
    have eq : rneg k=i := by simp [rneg,k]; omega
    simpa [eq] using cl k

/-- Every correct circuit of at most 113 gates must actually feed a wire
descended from a mixed AND into a later nonzero, pair-clean AND. -/
theorem filtering_path_required (C : Circuit) (hm : Monotone2 C) (small : C.size≤113) (hc : correct C) :
    ∃ pre g post i, C.gates=pre++g::post ∧ g.op=.and ∧ g.inputs.length=2 ∧ i∈g.inputs ∧
      MixedPath pre i ∧
      (∃ k : Fin 685, ((pre.foldl tick words).getD i 0).getLsbD (rneg k)=true) ∧
      (∃ e : E, (gateWord g (pre.foldl tick words)).getLsbD e.val=true) ∧
      clean (gateWord g (pre.foldl tick words)) := by
  obtain ⟨pre,g,post,split,op,⟨i,hi,marked⟩,cl,nz⟩ := marked_filter_required C hm small (correct_word C hm hc)
  let s := pre.foldl step initial
  have eq : s.1=pre.foldl tick words := original pre initial
  change clean (gateWord g s.1) at cl
  change gateWord g s.1≠0 at nz
  have path := flag_path pre i marked
  have inC : g ∈ C.gates := split ▸ List.mem_append_right _ List.mem_cons_self
  have len := (hm g inC).2
  have priorDirty : ¬clean (s.1.getD i 0) := by
    have eqi : (pre.foldl step initial).2.getD i false=true := marked
    -- Every true flag is created only on a word which accepts a nonedge pair.
    exact flag_dirty pre i eqi
  have binary : g.inputs.length=2 := by
    rcases e : g.inputs with _|⟨a,_|⟨b,rest⟩⟩
    · simp [e] at hi
    · have same : i=a := by simpa [e] using hi
      subst a
      exact (priorDirty (by simpa [gateWord,op,e,GraphClean9840.and_ones] using cl)).elim
    · simp [e] at len ⊢
      omega
  rw [eq] at priorDirty cl nz
  unfold clean at priorDirty
  push Not at priorDirty
  obtain ⟨k,hk⟩ := priorDirty
  exact ⟨pre,g,post,i,split,op,binary,hi,path,⟨k,by simpa using hk⟩,positive_of_clean cl nz,cl⟩

#print axioms filtering_path_required
end GraphClean9840.Trace

namespace Simlowker.Graph9840.Completion
abbrev Point := Fin 21
abbrev Line := Fin 21
def masks : List Nat := [1179809, 1311042, 524934, 1293, 1051160, 5170, 10340, 20680, 41360, 82720, 165440, 330880, 661760, 274945, 1598464, 51203, 1150980, 204810, 409620, 819240, 589905]
def incident (p : Point) (l : Line) := (masks.getD p.val 0).testBit l.val
theorem linesPerPoint : ∀ p : Point, (Finset.univ.filter (fun l => incident p l=true)).card = 5 := by decide +kernel
theorem pointsPerLine : ∀ l : Line, (Finset.univ.filter (fun p => incident p l=true)).card = 5 := by decide +kernel
theorem joinUnique : ∀ p q : Point, p ≠ q →
  (Finset.univ.filter (fun l => incident p l && incident q l)).card = 1 := by decide +kernel
theorem meetUnique : ∀ l m : Line, l ≠ m →
  (Finset.univ.filter (fun p => incident p l && incident p m)).card = 1 := by decide +kernel
def frame : Finset Point := {0,1,2,3}
theorem frameSize : frame.card=4 := by decide +kernel
theorem noThreeCollinear : ∀ l, (frame.filter (fun p => incident p l=true)).card ≤ 2 := by decide +kernel
theorem deletedNonincident : incident 20 20 = false := by decide +kernel
theorem original : ∀ p l : Fin 20, incident (Fin.castSucc p) (Fin.castSucc l) =
    Simlowker.Graph9840.Matching.adjacent (Fin.castLE (by decide) p) ⟨20+l.val,by omega⟩ := by decide +kernel
#print axioms original
end Simlowker.Graph9840.Completion

namespace GraphWeight9840


abbrev Matrix := Nat → Nat → Int

def col (w : Matrix) (rows : List Nat) (j : Nat) :=
  (rows.map (fun i => w i j)).sum

def rect (w : Matrix) (rows cols : List Nat) :=
  (cols.map (col w rows)).sum

def upper (w : Matrix) (rows cols : List Nat) :=
  (cols.map (fun j => max 0 (col w rows j))).sum

theorem upper_nonneg (w : Matrix) (a b) : 0 ≤ upper w a b := by
  induction b with
  | nil => rfl
  | cons j js ih =>
    simp only [upper,List.map_cons,List.sum_cons] at *
    omega

theorem rect_le_upper (w : Matrix) (a : List Nat) {b c : List Nat} (h : b.Sublist c) :
    rect w a b ≤ upper w a c := by
  induction h with
  | slnil => rfl
  | cons x _ ih =>
    simp only [upper,List.map_cons,List.sum_cons] at *
    omega
  | cons_cons x _ ih =>
    simp only [upper,rect,List.map_cons,List.sum_cons] at *
    omega

theorem split (xs : List Nat) (f : Nat → Int) (p : Nat → Bool) :
    (xs.map f).sum = ((xs.filter p).map f).sum + ((xs.filter (fun i => !p i)).map f).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases h : p x <;> simp [h] <;> omega

theorem split_cols (w : Matrix) (a b : List Nat) (p : Nat → Bool) :
    rect w a b = rect w a (b.filter p) + rect w a (b.filter (fun i => !p i)) :=
  split b (col w a) p

theorem split_rows (w : Matrix) (a b : List Nat) (p : Nat → Bool) :
    rect w a b = rect w (a.filter p) b + rect w (a.filter (fun i => !p i)) b := by
  induction b with
  | nil => rfl
  | cons j js ih =>
    have h : col w a j = col w (a.filter p) j + col w (a.filter (fun i => !p i)) j :=
      split a (fun i => w i j) p
    simp only [rect, List.map_cons, List.sum_cons] at *
    omega

inductive Formula where
  | var (i : Fin 42)
  | disj (l r : Formula)
  | conj (l r : Formula)

def Formula.eval (v : Fin 42 → Bool) : Formula → Bool
  | .var i => v i
  | .disj l r => l.eval v || r.eval v
  | .conj l r => l.eval v && r.eval v

def Formula.cost (c : Fin 42 → Int) : Formula → Int
  | .var i => c i
  | .disj l r | .conj l r => l.cost c + r.cost c

theorem variable_filter {xs ys : List Nat} (h : xs.Sublist ys) (p : Nat → Bool)
    (yes : ∀ i ∈ xs, p i = true) : xs.Sublist (ys.filter p) := by
  have hh := h.filter p
  rwa [List.filter_eq_self.mpr yes] at hh

theorem formula_bound (w : Matrix) (rows cols : List Nat) (yes no : Nat → Fin 42 → Bool)
    (cost : Fin 42 → Int)
    (cert : ∀ v a b, a.Sublist (rows.filter fun i => yes i v) →
      b.Sublist (cols.filter fun j => !no j v) → rect w a b ≤ cost v)
    (f : Formula) {a b : List Nat} (ha : a.Sublist rows) (hb : b.Sublist cols)
    (hy : ∀ i ∈ a, f.eval (yes i) = true) (hn : ∀ j ∈ b, f.eval (no j) = false) :
    rect w a b ≤ f.cost cost := by
  induction f generalizing a b with
  | var v =>
    exact cert v a b (variable_filter ha _ hy)
      (variable_filter hb _ (fun j hj => by have h : no j v=false := hn j hj; simp [h]))
  | conj l r il ir =>
    let p := fun j => !(l.eval (no j))
    have hl := il ha ((List.filter_sublist (p := p)).trans hb)
      (fun i hi => (Bool.and_eq_true_iff.mp (hy i hi)).1) (by
        intro j hj
        simpa [p] using (List.mem_filter.mp hj).2)
    have hr := ir ha ((List.filter_sublist (p := fun j => !p j)).trans hb)
      (fun i hi => (Bool.and_eq_true_iff.mp (hy i hi)).2) (by
        intro j hj
        have hp : l.eval (no j) = true := by simpa [p] using (List.mem_filter.mp hj).2
        simpa [Formula.eval,hp] using hn j (List.mem_filter.mp hj).1)
    change rect w a b ≤ l.cost cost + r.cost cost
    rw [split_cols w a b p]
    exact add_le_add hl hr
  | disj l r il ir =>
    let p := fun i => l.eval (yes i)
    have hl := il ((List.filter_sublist (p := p)).trans ha) hb
      (fun i hi => (List.mem_filter.mp hi).2)
      (fun j hj => (Bool.or_eq_false_iff.mp (hn j hj)).1)
    have hr := ir ((List.filter_sublist (p := fun i => !p i)).trans ha) hb (by
        intro i hi
        have hp : l.eval (yes i) = false := by simpa [p] using (List.mem_filter.mp hi).2
        simpa [Formula.eval,hp] using hy i (List.mem_filter.mp hi).1)
      (fun j hj => (Bool.or_eq_false_iff.mp (hn j hj)).2)
    change rect w a b ≤ l.cost cost + r.cost cost
    rw [split_rows w a b p]
    exact add_le_add hl hr


def tr (w : Matrix) : Matrix := fun a b => w b a

theorem rect_cons_row (w : Matrix) (i : Nat) (a b : List Nat) :
    rect w (i::a) b = col (tr w) b i + rect w a b := by
  induction b with
  | nil => simp [rect,col]
  | cons j js ih =>
    change col w (i::a) j + rect w (i::a) js = _ + (col w a j + rect w a js)
    rw [ih]
    simp [col,tr]
    omega

theorem transpose (w : Matrix) (a b : List Nat) : rect w a b=rect (tr w) b a := by
  induction a with
  | nil => induction b <;> simp_all [rect,col]
  | cons i is ih => rw [rect_cons_row,ih]; rfl

set_option maxRecDepth 100000
set_option maxHeartbeats 0
def rowInput : List Nat := [1048577, 33554433, 134217729, 137438953473, 2097154, 67108866, 268435458, 274877906946, 2097156, 4194308, 134217732, 536870916, 549755813892, 1048584, 4194312, 8388616, 268435464, 1073741832, 8388624, 16777232, 536870928, 2147483664, 2097184, 16777248, 33554464, 1073741856, 4294967328, 4194368, 33554496, 67108928, 2147483712, 8589934656, 8388736, 67108992, 134217856, 4294967424, 17179869312, 16777472, 134217984, 268435712, 8589934848, 34359738624, 33554944, 268435968, 536871424, 17179869696, 68719477248, 67109888, 536871936, 1073742848, 34359739392, 137438954496, 134219776, 1073743872, 2147485696, 68719478784, 274877908992, 268439552, 2147487744, 4294971392, 137438957568, 549755817984, 1056768, 536879104, 4294975488, 8589942784, 274877915136, 1073758208, 8589950976, 17179885568, 549755830272, 1081344, 2129920, 2147516416, 17179901952, 34359771136, 4259840, 4295032832, 34359803904, 68719542272, 2228224, 8519680, 8590065664, 68719607808, 137439084544, 4456448, 17039360, 17180131328, 137439215616, 274878169088, 8912896, 34078720, 34360262656, 274878431232, 549756338176]
def colInput : List Nat := [169301010, 338520081, 562157635, 649419008, 1296740864, 2172741127, 2594530304, 2694136098, 2701869195, 2760196385, 3156164640, 5189060609, 6309183552, 6599362050, 7585268484, 8614583936, 9869005328, 10377072642, 12619415681, 13195578372, 15169488392, 17228119296, 17789753632, 18943250498, 19734864928, 20754145285, 21761756228, 25237782787, 25829645318, 26393253897, 26845188118, 26860916743, 26911248405, 26929074180, 30340025361, 34458335745, 34952337538, 35578458688, 37883355268, 38660098578, 38675827203, 38726158865, 38743984640, 39025264660, 39470778433, 41507241994, 43026487844, 43522463880, 50474516999, 51657193484, 52785459218, 60679002147, 68916671490, 69482336256, 69902577924, 70334026176, 71159014529, 71412498723, 71480656160, 73019213075, 73421046864, 75205199110, 75768807689, 78048432168, 78941556867, 79727166628, 83014483989, 86052975688, 87047024913, 94629270578, 95563550743, 95581376518, 95631708180, 95647436805, 100949033999, 103083438259, 103316484120, 103760023650, 105570918437, 107374461023, 112777760918, 121358004295, 137473640854, 137574826610, 137623625738, 137673957400, 137833342980, 138264791232, 139807253000, 140667003776, 141808913168, 142316980482, 146838948000, 149268529798, 150408301068, 151536566802, 156097912912, 157882065158, 159453284680, 163545942068, 166027919402, 172106999952, 174093001250, 176119892550, 189255395428, 201897019422, 206326259738, 206410145800, 206632968240, 207517950148, 208848568738, 211141836874, 212954791940, 225553424684, 228708581718, 242716008590, 274947199769, 275040523840, 275149571280, 275165299905, 275213697077, 275666685960, 276526436736, 277345420420, 279613457424, 281335056129, 283614680608, 284633960965, 293233430804, 293678944577, 298533913868, 300817650712, 303072085029, 309444366896, 310329348804, 312194777249, 315764130317, 318907617937, 327088738408, 332054790229, 343638300048, 343867933905, 343885759680, 344213999905, 348186002501, 352237687948, 360786695524, 378084020228, 378512888009, 403794038845, 413264887904, 414540972836, 415036948872, 417693991748, 422282625172, 451107897944, 457414017708, 485432017180, 515665576180, 550078950528, 551333371920, 552448885027, 552517042464, 553054970625, 553548972418, 554062581568, 554688743688, 558651214992, 559226914849, 559419851411, 560637216290, 562670112259, 567231458369, 567859677184, 568009630035, 569267921930, 571269582098, 575525686331, 584922302688, 586464764456, 587357889155, 588414847507, 588432673282, 588483004944, 588498733569, 589619921490, 597069924889, 601635301425, 606144170059, 618886636640, 619913977857, 620658697608, 621169344802, 621235405089, 623948071184, 624389554499, 629268284546, 631528260634, 637815235875, 640110560322, 654179573969, 661896036400, 664109580459, 672248373257, 687274502944, 687362646042, 687446532104, 688427999810, 695880190464, 696372005002, 704477473048, 704921012578, 721573391048, 730149685938, 756098834442, 756149166104, 757025776018, 791902421186, 807588077690, 824904320209, 824922145984, 826529775809, 826786580384, 828074295808, 829079848520, 830073897745, 835390080649, 842217489520, 844565250345, 893624779984, 893640508609, 902215795889, 906858889225, 914830132569, 963149628368, 970864034360, 1031329055208, 1048044372272]
def rows := List.range rowInput.length
def cols := List.range colInput.length
def packed : Array Nat := #[36972148246572656812927934818980432873704067778074116804416231877036875626290134519133712097957813354822175012783728969301647121555886993448901573442162624023066751561916433860673279641960465560338848276115351058864864683054257317100956713547981212697009149317153202122276488482462738641634522809522293626695456727592375129983159900076803056959085915607979566163227528341062920449537554174104744298854378031770479267297565334067395155828197917675694693244414208049436101275328294206302865061696980130814479856340861675806574360691242638015072828502197050933737162885058321674220202614051554842437691468352141100737715302709310089519633817978585911285553468702338488668365797500389312577898626909826376136447559943086070081951041452307203457961741144736469441357492525633950923974008566518, 36972148242810418288084280284504193443140018720320424532422582203600297966734213443944990187754100570674593155634139888386872641527531184841081743958425540057499694335546661354152590753609605407490915963952300518961435456955530214234424843429038800274227808666029958818618757302993682484197975149263922641931486052834441759483724271582307586728594928951877508250202930858128708801871433847897570289559231068478824526638856863628472240919001194061161928114599825953601900917705659882693629547299682292875353911146292056014197137755164217138318227673028388304691974514772345312170167518327491410277551384882922507024084354386151942066072318867002444509478720949789473213928174117298600330769342410231293768801099930185561923671508257569985610529932440756637979736073866444243207060834153206, 36972148242809218913388192566207292112451999205424456218889199559968244308031204959838198344355265362530349671241148366473815366927734229743551745951320894794160041719618410941812412615578642515873492524228759254374365282807128574145049918848160604341697458108269131828438116095080906551246817326093481273717987930338735585486491582549595058979964095582899998637366540925525232467872520476616879942154542398695791966152388453616968281886609272292345093224167136748583242533488915309774450905243843478284448687213561484385778544477793332565018080054802771640372654612878491455899876485927674215930912994749053227974213463657878061093992563765003655665705370831718920610596351250272785817747483526184682748576645274954737915724827325163311545204500615521304108842191319394973862983900525302, 36974411235462934913102909367547231877372278086922199411937959028943117563014013130813065563112738725605199349118992749861211030344264085835157944638448759029699744941912394256620233999059060551784986751202148523601516670596558673230904940565707073110576645743061594610911936361648131456519636655313574346408466339188292549469838034503246291734724364649258545313451400193869429148328439490098736212448787867000896272219603567893207016947159753152808702610762172263648540768532924234206652368516809599807946940359531499385311923397364500247271434104733659324369671380939056678856111178162335727145100603898255220363071534805883319755476005353068742632778475622618006062822550198646227463585853618246478974559007516430535898042750771286390561418289375280578215630282650516605687076599558447, 36972144391817705505259038827544879976541289171741929766712642142673559762719461443054586095456386876703027668029806903787934990384605692966423518757075504871775917995038699389219278395840217206075134195973939743686759016086839607176924442639770966549872274730397092291056151572355002332727817229605473979666938005593980663793900398200017058916612394880992473745840562334747037400644311153144114206779689561201390942476392315962215317720357535083805066754102149069891707832004481284245670571788135215224858996764058999617046636461710019617785301680386435522716436288304629514101055570308663648183146550017308332694287200845029844441409685165231860063120448330639808168937813656606454297575741565297175104088989610358267014115687193300697274235256359086294561433253496130182530077728158302, 36972152097563199370796589980993941896975714580414326703348259777962049234229018311295262729609074509162193177671124804412432629822774650177485804573662764579299757635277581713716285743988251658180797905595721708951214433248809684173300935241474990299840518468600067324124259516205562918167676434738127663116825735853562677698884110090292960577152149230707152667048931362206351866082340427116772330910594427132985466262646057522950052217190774984993444351187596270333257981629720951677592108043365662901097798591913196788004635488500911191501517646657651010700835883733808221677415491579986705559645906266763770702492953896029778968260226920123164863995972796537037024369539684617867234729612746284451831375871888541938828221732954943146067346002219351192604058069078091936465255948333662, 36972144391817705505259038827544879976541289171741929766712642168318730657765907382967497740719092834555526218059469511704116440850851948724316498908083208358249187908383087681223648286771160187340908097584064384017361198324828046678627092423319720993889689916491055447354675847217449630350485460254684188347410825614958912218774258398918404082466297452669550682274818412839999598882532050137853316481459077378891642851303281590314593189301756215805915354569213754858908605620230516904894276576805838658734552905046531769819606026490704212103348349463313433019531837256292709035584028404816088955089441635784535023048993369520886908488511749466753941861169085137159316719681484671684440130482146239610148698424793232114669652182716963269330057354251665114428320224495205211599905555460702, 36974416001971869742070114400968416138182613526449290296840652090177625078101493161192329199027907393387194190912744833433630225499085090496782477432015800571161090890629494688822488681013118650343965844363368434520801365249683632844058134260140733951277727209057179922696257934289747305020156603359212103143777771887673715328642705549432074804671020364023749021543150955193410319656644166930639014607221132183077652237308683436276976369468959293589187829517406942058746923867731586485549118349314097372661219955004389226374020587948666835545516104718282013331147590099317452132620322703722792180055500698665404116520243048004217996672113377136070959788390660231798610381030849523933007458200054460471367358649403680684957227283455805937138443257026660393136276640735706597500268755647070, 36970624414274386059912968743238693133506307265011422435158289482674829364624054815270610978041745353545586721182287768339579774412735886052398737451481424249420208374396831944160491940486480174890695473920890521070486527463204571323525662237845585096421294013941498946668318125469349135890379216909322255271900034366164329640815962773555934640072386773076558155050871285487899656480277704924188512187659184843306809047385632224654415197972658972638568661144318328867690205088408023716478815956140469075377899932680747550572357021437444017828777094631929273330306072265148951292282376395208925353436797936763414212281599343436297303474830520746285953789855034351733975915809298107973301079125491959398566200060624176484034515249206373578771375385013184584306830368414341849311737355104862, 36970624409146267672128957348909111967307707990442510137801815565403486410920751382383268220303416369665387805341008713941584633702624831084661423442188360988040533000177412521046848730200638840884368281368070686074779525607255395698908611747515173261452332500412787074904651916732238325521508660952671601642244591030338637438987965526916915365059112121691143211068003788236501098410237466714419724719202254063382372175129324697933956919604059243065495577791045737273606581034042825030529410273770191248672957795193377683231232100541410928134926455087190650307222514899208984166174999885807381489839871436721409563486009401118047030697500318676513061442293624668508612596396912622035878977106819368554415312289231047132502280601852681651890244580529313779409181537461176028397982775964254, 36970634906408309633724651701847155413781373467556706448587438492118985905059903813823097246543782069683235412731286067121862426357740002498847701308705515471128971500050992986645630719908110639577698286557287378880678055147753783112135550989658773823716374519858034203577111415706261573392727969426060714868114755420513389442633381396487720403330430669582276152095725897149019160665035963869501182930732801548094567453900990554305368666329713045366737519523234642716319922683324226953784728271409061435673173274794156468883077464480288177460726776717950151399487319166088279059229998211111353526088426546747334474762173859896067379583533726649798513031339650099716791140324783943634330811817683708031004535481081451030672251667874714920164064033109406735110510530625107739980585881498206, 36976941988854446958469921385511030482137778309453854730726856683832178932413117647297536674805665772348132260688966702881524684947023136249271167302423353423506220308769994737009904856986830431027009755209527662224140945767675048750857848994036209768880685012868870920830642978245446894967096764305505876829404961265201221103816862478572179824091883488770498264976375906930258117615882938969546295292116112840331284252177318361089251340962167597793777565055727463645448410010819960492262295153009571043106627629785491269011950238883122911899695670213644091858924837749048283230063988444961007457684132598873508003534863901605013789092877971112064087686494997483873552314970383064034743053500896941374003503806709696394534965211936305233587429798319489601446896535203706936950622294045278, 36975160888420621790900302163313867411040391236037955421630613204736614806114283943425012825472953635487851593810519651943662726019249905698158706540976814999508720598610531500511215727268134749471518208897852058382748493939277065253351985449045015835122637956556590186773424691769611459995489902413883155246350034827593255021344415394832419886396653074037542827424282524488753615569889531568272033832051855124996330043401952284192334236741003102223605087672994097790809458324208710005327264072768959613114288390707249892328186497514777018302169746927291485354860417221683997231526569633508488832433643257458398427260480372125901316489426868084628860851006127551404717411607876252282769521191819029220162654848194597660579608919401734140232709319817905670491480431849744888746840803177054, 36977418625776462972308242532727449985753184768110040963486862960267066174671498710840072084444068741568085714660348310060132233033520350266304593089593057109987714610816759816808196650844773690712869928821164753348891935301697824982141487154143253318050656043435169786192290108134239720239707621020980449119525126434458715209966698841260778289272337543515101843736751411029655496843078709738038300942419817727401589810206979773735297092033774747214528623451500240428009095241203390494322316085840776565454599380115891199430624065127014616590728360903397287069072208117984907534409519646513275338020684506829550121560300136884254603218773914225234951793947237146740572706682727608937367881236017544019025709934834768688585748629977463599896177477932639455826481284778436623463396569969246, 36975160885751388503857116681532067175997203776506585239713450810679540565703105433413187409485006596716223819078072381961839151547402724989967241348464600086342433011773285296285755967754885275859154382771124066635152343417964354328724941737802089840876279879617888087586776265684668446162717700785842248418572799478119579254033716161353706324213787864443340703362070398567369028998274509172440504994965020507125258918187228119122490741095367781530492896993283063382915795423271118971702677626285944354555080909792333448427028445074403178020478251624430839533379105590334501040327839154735598858708910827853287365427829839797805325552358774160975744535267235876730995950708096075462894754679951058636049992075946122490617200759926574386388302164754613615002160268098191308732013554627166, 36975905289843119026507577084503533376426104491864562386919244603693132844350324703698718448021148609609259380197836985570365636830443357275933364170837841037708763036047810188386397273753493473776488413535257834576900197655958944900911324486043759365851859051520379418820267152857172916060683895523585144421255157522127997687479340619266177532433887487950106602373938836965617972887711155990548076137896383910679008591840464462772656036937654654263197120239934868034307798358761897683307881676846075900960907612816675274003287237515993177930282714496511361805318032004748800551189714303353000438675572080131837345096711537533070165711627401611163282619061944313213209434612654096483594456529513899119647021240667490563787805228048271502445028952845541156807745164429969061760263378891358, 36975906874609645124069140220557447807399447872121612228157508591841865925594584170682642314415013024522578388366819994421146066508742538988934904987109730866482099300475460731591381463197376714735347972845060267988614939654233332267418605096567602525745408804242497610378589039941459738424872108317939091619481219806852580633667111443004811936188409316866524765301509170094519944661239324096161265023305864965749356163028103018067576066338032207053335227910960830615941899532460938013742941344228037351002351905898370769527004526177411525825904978482823778976770430200093551319667304071463931258172851153986636720625552938963251121381781809797337429840353957292351460669756184413284466054524631015907342612435855015847169373992706766408459481443589016867814468128727732566435330610360926, 36975162470730890319603578620561778086809644673362502268291305495508619981256715520039258843072226899935106675567163866994820710509710591780549204115033194390300537962365819492121396320474396286852353946048583109537942667590935269001958707350095238502954103840956162213278303404926642937895853280002650976132141062052605708484636456531344678628230423188065254323034932947071307537042863559375102315776336901218577757576918614830609522624631463805380180545912275943502041844541857589526946854229344982446896301969902410843497345329656021135317473042351097190234835124125662078186189741076318188433283955974726920999515922278989891812541116717174463416853659878427922030747886657755185999452663217016283056002320662289586972828135513565903416927505489887736030269443531084473022984771269214, 36972153495883733550567810682847361659915571646138918657988779058631103350580513047191842945791287248903490713997997022893839979591582828633670529973111869736468225519558143422143032676305809225316809473829574332538414870504957117472842378918546685223636549381584899504293310187541939451342370711625508706242590146954932429356604803584917720084852288514594082597745642587707688370587603512133566699469721711871759132996767251416290832798741965703384636215237220623874304607389692632879326908396457687761652111821747752986512554875757982514365169567496550249792560064341027708247150719744272572479499547772631645000456283968685205875278346660913359065640064543501411737949954025709642798971090659515195389401908492102200908774568153178526632125438316801113616596126316362105911066871657054, 46241352760730563064166929069466076111423588913237870537195917641810847075786796500020431397389143885806417567222170387313089676452971491809523322474905507701745419129900901972780233210606104721494788253519188900189223133753568643214239705523038008135100729046223434956706057048001861828238321824759644979362596512049039770618432118789649648648101588231189800095271915584806129411261414395279245921252113681726499807225483822225945817395489319107685620277963634068306131148215612770421374533333506302393996014026483728909322943122743589066620767586566475067013907273135490236355203284735597883450899577884337825408189265703262918164667544633321197724493376840071102643244394852602011218175389892027773600944856717990908489069924951752975568980984766739316062847572842803767081629912330846, 36974411451328024860008690872982279215331717711142666940385932928209554093712798874584139993728500329132422961442741478919130393962963037747673386786312579636956966991116107153672131224947759020737785823084604588461846056074063338978841130079756706431164056921966436239963671393860903121581907156550774086882427778836862614771584195439606701257429498176084180607914054858750475661740111743458791185563432200520310116340649010193134454387318943953788288048866103139987484651389993554175840167743031594052512808837589875001501058325156286507042246863187879634464972918808086391001305275332866964979089430958063317703881396465604154508860667760654780968113798810373505663952731145701446789120557436480783770768584196268539044972123079412884432160819311753012232999688039365144538303048118878, 36972153495884932925263898401144307124949553889289025151652303645111223510330887425423152949932006415709531510173779843809425632412775979713680865764387760307050451116552963082188754327142311735359085023820248536045586754411250256157385116529854201108261168591138612589472816843223108191820133960969980700796150108652503374666226365271490201011406710669305845646378166495966529269806529770269390252842048997912227341033217967450091860859160130122702515173904404234218009554483161683818858756353243312486231919030477270455892105746256468836127588834084030944286075016302216027908488672869148527853084701541684958941939868995367773979706052211420550593895161598883663233405185225353299499074818018562656021579674492342428196379504206930332156335761904253506362277180388759368120216109380190, 36975905554992367645081933483478541715189103722037098890526487002139264161550139712968819578659558583117496029141770001516954300585715600699171702820548713845146339998691959681334291535928904957566856839321024587154354625494354837129121784617878228766058848024023809120038531546938710440294891011849244952943189741468812690363099332488185395461189146101330783320989924987150469559069549422499576995138942826480383446012117037011105211173889509130444622805255721200807214364352854963848022448998309996893113786714442048906310514793549311681336998958226331660453088198729386901383018143105988463390491164413230686842681478674587641535085090035675462049190398422749083503576789491161668306609517137531865354544889551558208242724904478323285980463022977308251041251739119489756393579125863006, 46246624053910514066310459013905773557490260784106597713860940384882911451290194888378883513108066497333647808037052713711639545501987040662442117850485789111569605797590622600890198016290877191236608300725728136755944308261328731706900799887599592886407166709516940946199289747752714433678980265328721019529211301826919362650998754250468297193339526538402114946632345428180509978889410648220591107822796774748684854436270380247572676801385114462925496795280953828856079743401013588065926327859832936058791793416682276844370016834126173324893384669829229142203602610477641067232277171925355878018007136026834017619976780644438986665917759429956128041096357697323790794521154128943096248721182132849831661626970353068345900725398613673889339731396828993796887961373118432550710959922147934, 36975900257949684762725136273185994689953266020313564440414029805712308451652230621137795554346660305112242080983382985283980507060743194800468808771961072327912320403363986012884733057998410574967259190716551334449434309857135732892167012145106160421820260028396320784548062012148931069279936322822237400280525922143252966383033263988073796662362229539918512579139880427114300892878910080359637931457540442279034726083262757262515309564214502659422806829056246017410824750387669679102604478420254975416182223158309657293251554713095019642970295052179041961184993192751921024719987760756510101824640703300339294222269448398371521216841787108780209337573025659978330435027667321050776159553098516668704067430755660351905254763419734387300728639189112013598928871720538389384756661813703262, 36975161150251009182064780541140921261842135796417812106657094832018688522323707617833620745215086349859884539870244305947892705018480485995295676827597451352519333989167606094297113511791381623747673506787965066813735380429051858356290178535217529486228275807383629474429517353977969088208823322107224902448024774281473207418168351434055350873534265990490976866791183560303984438518189302835878879957094723405674905806519068100776242101550045479860785827028568845287584914727490914994357858823105308108384093602167262036028724521171839169474478304751573413085382338551046195483319033400286049363575986470536912999570931352025323942695840478619174835900998405542000367415260573992066225397384549414009401348844734880188294693816747217572501291836960196479666531690174932756296746178638430, 36975155852751783866153909479105386037707301594487253536015245956208842324003748092568337718012066441248625612922554153793267689033056610542884383278895421044723463287171568979561273865525287104053343855120505865791110205969310416381388397538252732241377634046610315704444707008310374898357159284075684813534908792312311991670240257176711667429573209780604219291355124980319896832054649982975492587802126715377730878729296922502497183302394487659572300618252870210754422032060964933588432604498595867666712331706562354606091936818095027003809850377943153118930508892541289540202750949644329274519539365867587156351833275895059447720927489084129468976615297118922495468099689447049937382498295343942076726326764617212591469737016249692094799176371979945602177922490788513390424823323357790, 36975155421703441716528459587516343344987412492105268889521498888912643247964177013006154435716378538843797729450844946865546139462292231958621953415359518653339238776509984318224943972096925668538226269786160248626345184802166310251790202923047558446434160259274015024071568683581374499480855004708438755177110379780021255833654408736814853657779642848039138778196910478443773126092941513774137088742677112258655272220495468317351331027266536504742868319353664394387510807117081918865183982982514941848913013862526073677525472579367364475419025567610185137455938354656381166800147693819396630331717973568444747771089296188565742162012106890753101440003486453731385823292613420075001942661273839607340998052245243153782465886417174288976765677778181318684045571998830085806018919627158110, 36975899826569867952515403219662398958003830594530312354080460932071766808050739127845750949397032222019761343004208193974249143834016826906631234059999297174121211277118091333603243140095933532917925872270318709308666702246745176036769592635714996920029051683630072516097195647421603719753968594923310165318623969470831117192205041874215974768345698698615982073181463406483809553250507261781379008818693186691248231502700461286624381982019390398101432010390250720639834211283320812439839151334599726951197098103953095950500885187857459826917927242949236101970517896331555521156095484288195129548904361056417333280142384561406960776152399427960171678374385482161540822540986359495634221322806734018803705344084577486104400422467520704299542297819671386047674043919765104571881397570171486, 36977418843755974494662426876859779605576160148127240817572905361195350265646551271781391699550498036517616122075796721514047614590294178498839254537079709175433676047476112681296635427667036664685887768765520605099523962237110125896822654600491662829774445323589479657930076582991691499845271414456107009259909763660748675494451937830254171602313180803704657634343988837549178735152041446872421016302732556287443096046909588437313725524877837082678318438533905115318182542366817718394220398067775064298393920115072152725167842128763420547665226227317273188948850650388871190881376777874562118803104950000273327397078567960736309273153109057417469709386751678369048681509315403302851237362389602825215477835605361524547579373223745102257469848892113723241643708068794979886861766077117022, 36975899825796056172194663581356071259945053929613781031382478447881617070031817944094563246878724002119853241871470476502576083820192961074715187246307364708862700672210187142494840703668839650103296589630904127674519071008632034569574531774129085989962630402147110876805086035527658709819730266219853081203863863067286446182658903748967596428961353590142985819912071608093830875785156328796118698885787840472492815599764995537877149307882101959646236576168177949318144153873630162542310938834923867932912376237921244925725937364000891380151515410574346849210713146541953965210362350827156792568238724230617436303989361067037956467592599145728152159575211476988844330528615814042111588222219419871310316530526698683598805380537777132758363804052220449151589059321171283917429123627283038, 36975155858651526734521156857128494242972276271626468431833801766693798313638082164016648095224267121443175663740652074621938497442338477280217118913549550276820014792079562690364280652159097202116091372773483053427688411105672937802401451741271115414559013862792515856350858250875226878788758682996723812172999503270911515582716326028881988630126563792750091634884650493541235604717989196920758507680113759907604969345853676690207808545136798132120490139783431753228881014585155051279676734113209844612035229509736152515171703104938693881644169710665579638893713125457203800266331099889973009941130626202274427236620508100132009861666198050084850814295653309342745006989841761843582162203724422016998958361774600526959098327363405020724089765863871117749563086215096976656939746539532894, 36975894795251468130989658836862606130519781352092684566314785672369706465681858506759341572673803744000396234163268093228045393807949335792902120442437689140327422521011398374774694461212717060854988006424489578583479795221066358564432093645362057956850937856840422060923307327281178172618403640294576468803891162734792421546579402988814665810491883294317810129605789659555559832475422644864122029704472695974811128897073363000348924926968415303039887713386050504221629393252201149381338139223723445838670100202693142775377776950000902008871600224562049267533431615857337481828708085511116002210072542681411911064743348458043459182572997161457396013197130116334678299367579877836572171785108212921106192997842725680562852211633068153722088790116272601558443187179722002373555483309175390, 36977423874299259169145671557469758053557136080125253087524190186899154218071479815522526040218391052940287368008495935654677878724492056330441693037271476644242911469992114397203806897435820538189854381325757300114129786007994691248309967419579758257615764534120963987536453037460524789170086236407262113758113223589991567348859134841212746412612836546021578311683881849686075869853845153580453477976482749146287757126790427936342871130863031948682556095445587117404776599511815570465763378646012721600019911624343695926156836111856955442259147462274894356020872387490903489603016050595032006636164726866982531406808559199047510684397010147063563756919097805286593722570568018656581404431399136631677893187324382009344876117800130161388059592467449720321618028534388020375492843277578846, 36975905293286122497948845467794578239004947310977423928638888989176658371558479464841667926478228262893467422579490739949583658147188916378656193317970994988606644319285491009595959778852650333704767649380501024187377895126383282475720663361538630281643054860568935023506040320208756818466602105543118471108118036505610896738989511672452164382541862524008802933866880085096343850150202544341607983679226450807912529680264213127118848995744482547067050703207866934173447222421430862758544112037675353080688428986714341867411741816514576847102068194160708797616006228150439739021161079507753406309096874906437517417891997204100244847620198116654261398715749604641345716583018113754880733477483274137548148306413213055478659123717086600495898091115277438506974703519558705075063630331048542, 36975155421701864504139095680507358104211751568444544485554835769451178164475381469211090516073491692123656952174289797852401532039277963717661503586919546973848607855943589937514319391307297907165429647958135593890096079954231770780722523146202380246716794519003680714189722629151751968871861540382138630574369920288902426508009835659261141967277767302356139625478483708546772633925822745284294007887250947305328665281616877315479709339067889278385679148622873367396623780355460132332691067078108447214302188539444840159074855202518707499312041776502676668104516438944728536219727304396370573934007453333370920089817153584784846976074469408228236852752148246949302105070669574302389644998018868392139328616963887249223243346872377253015394752281626558206365052890959565119763715988845150, 36975150391932391609976590638242765707617886827570439043352969253037038790949784687947619772663158332294418207491027602916563740994454334397882161415736581506982216649918864239805779410644107013673706688325920810511417062279050032408671236488606990829313436753290273041980900314259716870357442061409394540972728096625916830423813341738537391573941413533800680441638228426903458066688931285384656054397250872940815717111231004691606335688412840930467688138965486282338998211976832844244491166422981206045381958682553464072693450303997932605242501055700270004631392606788590966628208375865432657587409742775367549379217944946709958247627418589388931746820435008902804384750171494563672847925905283416689516599526470199191231009286100173760855372397759329681487723945356141715361306869166686, 46246615436410922029939515940974925976372111817260986806359509298638086866057490949060182224980088255300153621699890487322983308903329681043422847765612106492432070185451917438864559971976289445241201463143859867577991864395242422907431287989481774207739099419586972051165386932983564133945022750510483470395176747156400739546864758252664351578766970631957081597580524788810824599616764613478826658663020228225772763770536381779446240351979825771268426988488068594600307969220823855809305842125208673232175834071937566267250796271540886897317061032200933371591143615852281438604368610069416912433361049748661108777217433224453150201296914453202913118734011075511237319301021515499481199385077512016602879944843912496850109167983337629327521030744544672502081096084863123582990578336592478, 36975906877406726237569250216866043547628581556977068058229370127612219454460474923639937399334476074846770736393410800679121799227473898647429902056496880494917958046405131967133152757833178748771386085826887459794447622601463868556736274038786750416679628051346796733160601931925472958781194917053728218397182270321325461729774608900601495789078512556703194264138688982633276745440368169828835848979525211444682964749093741260000734855822397547738481437198700375038301131127011831751048614541515263803452023274738673937259269118385951075777902597518113964862866064397517370240337226144262358852232818698156128848572037760133599253153273848809361213005334154466540104767133668036006993549985917331521615932010380852743662748121671322208608147817871321252549584925358382621402518061773406, 36975897060901472995804425527561282932188637808326242857221427412187142170691037392676089237254169311823962078605400057993435331701720474854601983069230864945532013375943427501471650082942478630420176649469688065102838720995682349836170258742172512786265263822457283652813680175094561630704600048191846718005551496569256397232002117700831515406514475337436386393854931727808244140867275636117920979791172255380433742760826612905940157481972995236269991307320429665295279422817844249633206133721016884454879696083694445363433493868998478709462892577633005260238581975145909284576392458026350453365583639390244023697716703016800786665541946175401994104437029399909780625739033597282659579691232484634252819586888389361874385564165279277587469091015946685219203535185305501617399911666610782, 36975161150253033560647184999053789208319216368406387195092970329212134418569408124630427421852950316997138467344971255067288972883926968058165936407441618085987077070191298755148831516324177067801483493847562250429793853796202990086535496491358219154224589982081619148702302578582567804898441183394241353091817874333144626113200778051320774482743111255002590777619842664205243042630460065631590489219637549595490511586070595669193165156994985814179187922532155540376561887348637340690528362805807394966945338022483460019576689980216586717977643434650712020875394748957877326424486955277648670649787288782548000217095981167541186122633484515272507249269333976069753209564434422753369130854723963494445912285577908631179031323733156348877793697675855008344638420864041823823037398751834718, 36975150388703521636090352234390810613941440236796803089150050544125918006179241340211814146814294943119423436936340745150062465884707839237492584483097243372226590330263447581457558219235726433452650208104102831366671291710080916381854130860988228793908921407767466402245420832447477076550379470087808613115052751328372492982485860963999158633352681437031994047245408613424918139562712391846007175843602345865703615474750885155889499213110747034531155038053423094749935330150121657126040218825459217490246770863963798358170830448169158755976277573458657131663741105835370226058648107055022816002117355555599709603465581488555807406142968823733440239657478200602406184073863050287201813108760285312135427367861552788530038786378985665685639663142860156558885061114225391063131282056868446, 36970629881118426036648263281736747399462030887791677222302583171839610062943508021261765862437869418556450657051290876322966984768990108617896672525696973514877872692871883983156865506363931734319115271664929628047789371778580713285127935066271065861730311508236323472357442299000788212579895910128190536842700202269814939813224304058291107596168377447141014380967272060523059476464576774296373693470207495126126005712137549375195280443022985858500629700657839638828318043649483713357445796694968059220155003302680929749450539178455254751456723337653453011388293330631826489304299828703859404236800134516238799092873911540429152600332938366216732918540185254957695626480743269994698107510543829939495051985545122255474371781755069088532248421573120009938810502099838079394724487489581662, 36970635170782169259212867728940972225865442470566745875417400622175084959373646608791057574827724763649540999875921719977274637981802940501403661912712351514989600375061089007303696496960433343668847109339883023017100056598308284471174265956161491975849808425582783198384172523797422102518528209976764942458497847562807183982103779702840858456815770520973058140747254071832676014404297955807111930888927392331762551354385937701765252533419172329621983512982627950177565978537099706834017735582856350333117241675664938845360215645246907478937610924421141007390515491882533615444580641899720655664729820406291500419839038070526327850939759669923358913913220412230701566784029022767980087095983104668597658557423087350816528540856258282554486656725427709229461011551875600529317093595869790, 36976942425242895290192298745650221425493046334359318969488108083309303131859234497593986551565165496531507944947543984473053968835460174641398808312914670591543120765268512698870916310771150346611223477590001051103080602368117825548917349854573942152422729815141593035436673132445352687834983912925121193632658518392938314753830483940391635981625696900034315766824179895574081733993097811195909908004879819511927824919755741376909911887058047310937672179691741882929988491012289091027174942911646638641372484217556914400309067657686318549920819436128612985597255975461083601923353879675502287433421127285996755482096132313786238998610680363644293364682173667010703159919025991775778789283614381267661802663939456725834895689997837384307095430497326645879195869790315677594151563132334686, 36970635173366378645499195244611883665770881643851917846969627623890901555128080340203884049434054768814558491519246127439191679126005838374715023972393890498652219916642549832983329268231660679840793373974323890176841468423958182386042149020580440862308992382426637175496581121230926525508513324467460367610825322789089208623218454331532308224066595160143234221579128510719881511892893035078711785798681374534723969414172442138399456847177907800019371008157632477022937615339270447028063628385653238079677185314910785343900416538451807824430004157389020037466141620289564570460443549035052196659159158065358602783928221126360526403429372633862750851909153824405892689224414832284351376202072076963436742822635799722726645449068400075237747608569951817302953823577065512664480593638257246, 36975160408393448563475295838941726396914231550495797772618392435381554955693263858788013421693534373660257219151996380779065887992893838419482722815811735694909532845641643112423120953028795716104201583440899184838063045100757515175952784243453680962352168229508790253274426131520249961139540105396384573230076950273815001689719733091116547861670291246552241899971043364312199731769323890105728864829576592416999994146038636292976134694179399041216944157102014420830815280187415060081121594806518015729208825105933164554432492418460130171869473994813362764792960593713448089775488196118760920258466073088382702948671304033522872625084530463378343919809544084678617478610717871524103868184905433231822905734840253656030725457924843699873698917149802811100194447483161797530062586073248350, 36968371920528472880497485976423912928716959538898115198254859599920574503587042374652790467373243080944426691552847086599702132257555087028901851224095700833064854961285616289572441561633813172251593990984949762227847388091408452878933867958816049296864488203967056499908712674763781489361732635115536299730057332439094790057375306897667868294609883989285648776557795828621528191279819610859936802419066669212926152512941019468619070122759019552177299732613438253678345457480143651754407537868737664144361869907106277173096999338052111029828420610227350669195924202941018766169444015402390057297904409012057207927342063374445211233129743516072617786716049769955893014035046568729862340939615342376819484248204605393809885246666895439222945766125481589649017048630409651740530037532848734, 36977418407476464768618804993320064893184588941995981354663723080901418041063192166702376255846136362808553710459494529076045952212257237799010445646500865035409235316659675708979317982618913720837384204676019791239881602710188993656257013905591879238478660898405920125684302695692179619468723470146343114640089788572202831623229395005307395005530063964191259510332782824295247205462369440348779798186988794924711692828219525672551846628127707363481076486864394775372319870293676892117206671198726291953205285530033953865523955102469702840791357225074300643853588773269222524063046906747055830043968434753732227428645694499910435276920134240244810235041969275357772277010959113721307426391749277659423999550009664365107849437178864192248431001255532078603783363262799565061337376412070494, 36970624411818443934877196420951192675799792886244965311454879238307750498217382497626127119099136554857854685368465668828794393869173857478496812096912460269101113240089329708241994286112993867422426216597338166648864789420487885820793628145321817190493299971876269696726789755535978048539852261604135865876409476188868232198164103209746153965025341807371749393253528071641464210338142153185405913650198758837220162502144633735610880570970993590186424342112385490913458589936075182794648142964972414606227914858702759059410070901819064506517043590948106900700579108615549214801296427812514717805215846566697694679495811040193596583187981353921509905472290416038442114834018580887816405301214103607908706245715173836897255543302760858639263075750808094216178739568984270383758510017147486, 36970624411605468215522864410389044170075750164508608247068538780040785520107009724597246067887378024473266814137810854723244894651051485240293633583182928099480373997815140485982354752578497144112333356504149641866881848902645266235791145577913389882390095683738278556226707347069857207052974972532801707173977265835713259033344143966615171996049328061452043853196097205706887061059119678113902605560509416060616600136499356836285095995346385182587008710233953869295143121272213447692621299354726668322975246935644446275235842461052487411505999640151034320574548497870401868941202642928796299415696790649433446465526250438027654043347464105539813952552118514319870439383844589233481271183114790908991895113280902812205125931504534443116370787481596173900803573747688472320538910452281950, 36977423874406998400128339315758952978996809338046567077988426621265815300054845904646162446372230011862907108810578682340558227832691355819419349978641247432880172211598632151629644425401569061199450229028625866669177817299387489691217628112180781970319954391521820096470013424018371333208398165268817763459740534964915211460638055788604589545192700190564868172459419154969025229950839249800504793708144583793759455943859026763114438461378569198070740374149548322569987270976803940471813305113239880966771171872940679617298448569431846774701374696302305155086492042849618907178761989848163036924883351366005086907303867878618389335547679665122132882741911878349972665081460790508465773940661641863149071963525000229278147058615297889940380253338720153368299434396630769157349939921220311, 36970636492282309470956004271355194049687377421652384362283501410752667558098344174112043769240308753263277441710935800437853870274412638722544748851243699547217382358622881659716009160105735746731782251144108810319851524732613455760964486782593907806543419943072996825123867718051281691595400063826511718947019336260795702709002018344295313319050537989561473813741302586250196275662489694646696099283354524975932219791941316444933467517270760072054486331041176270621915550129414826505909182465100508348393580328149482783826941156714051232989391449039351546810104378569813137178892209892699003247567991887121116557202681636803656911286097738682844797754414184019261062732438563829167727442081978423519555244036326640024418144920646843640284028345227598041853242902169766543355187012235870, 36970626682505889585119246376087725711859398989438630575765660092846480922708857765091017943892814829552906360157131317631984518190721676607762968891003163828293453313068122407838883338286287463075360443606654608742238796664463252473252906037642947904517336248950149643931817486345216518879400845214937244075122553086260724352532628829728201219735993134931423186403079016585809806526898488086018483501376895407071307850725564842282744358982477604428530561194671282400616304079255192761837742356751672819427775305275902156242538492969334863165477739534029046402349674926284225318397099020452855365149434140882310067684294747314973694318276838536840064231504670027511216089490609816773803608406095207539430745446720404518983926565640281216676746865195281065784410347289013266537801906844254, 36970624409146267672104163712045801018454024126704433682576022461374078632907299591872772254447247715422499625477194902029669224439576664006979442542416029218233459311085969625744659212509407392754551594037450608027463211218344834126458622507707910515826154578477089791041399063569145183673221194101077029885113123508762695347310415447853078765677309668840938895868813635114958989787021785692362203264867970346121966577256134562931599734674705546924297773262488362865115919823636798425586909630150428442751163568232585914410817963628040196693816872752407888091687128934923850761572718743581595136893158437720029059825785696523188033756973031358414534338555347878726773053706929160100071972936659684536886302720371472527104138949420793989698042982453258554041862668755231716050632053027422, 36975151782473360221237678249391765830970755827120366011356405210082865397900535966655824312893114155728922654154306229046969388549849590135076938618226764235822073241594429766352616086278469725926821734719720883296268871758144809909173431039761888848819102123630564219781539156751724875469622947492293927456856491356404823931469498601081644136705202969614460527977466050873223939838693629127514618633669174066911723063999847731434907848454810548000444053415826822339024024978620472976120840495903602882671366370065707421217781897140614117790219120021556106062532830912430530434068458263048205556494891758915590657017560344269745025838400001662402100489050150435263976745361958182034426977248708510732697142140615210154403910252716069438621761990413115769901871385301468903932088995213918, 36976947720722179018448627339957518309776255088767733210270501182598635143988025555445550201078946842336014666170725310292542032952256239529831264559415990835782445371905202278987090855456514156099665387666212714797825445922522782471191879403375188694953683163425764525642224868592227229081828991847767207527424681075258644346819789551926256077126523094214388505076462904676182537537343265515690592383178410468466075212605854714455582731153605205718779529171544316327666507915675560041180142426938826080777395792815277367994063099250955418597638174780743196632155014322716506314155657750438138156791858535189854507159273630212767748547648005719833676363443962575890196231139753112135293326406502988646304724035156281039087008374734257266169256853574755995759503030229099764510373117868638, 36970624411603787010616914147045843077901578786857727836553388704235517894713233174015932077773022857383458856393324483890433405620705831272020083057195896238084371305157566137836524761658943712048331721657555181950901207700092807704200577280185380629299535463497817847941443391684885312387334455053871236485628899093759323838577619282404434057325566880464887559224688151262363355927706049573716814452846395913448927220443062928606118843021927986982113771969352698596816585226491302304467991492417686222940517767706089408836645818399766937843152332304124456153472804983730008434546920436720117678014580328249415864340759898621805358929359400735446738090440674037551826196596001205049204812358216262507824138930302135272522934475443763889797944461987007150305921175587977320112817431573086, 36970624411603787010306167231177140071020164649738442858048609041312488147357208089500620658669082260061183663751570629590054005586965309036868850290319453649035313335158177614534474571145148077618050588023285420925873284741805207634284020586649478336375601549456971093997651916321517121852231869745787171169341842919532858360540692297165425175283905863042280434258177139784536439953334408131652296305151502017227035852207487546750828501725590553567304558652243706692492571807168061703449080351480305547117421464372691019603269876680075367887350999346031439805345734456452625503064822418310405583065876007841494904563571385394126123723471314174422332442313905053498181509025196641367344575749898687077710545189359139723249432481902533856448059770046907182204029238094829480502133183935070, 36970629442147175676553924615149814743618991517942372987830776692086845590783207601095946765173167485737700961945891442566443623310395178648235197848095805352910162116722196795726729475139216307197906050345245135124249624666451583245562394013004967826266183471236274414832030450681646158070016953340765245550899760022339667022710787385746735501418099662604725293584828079555727442629884153931147473578433317620061644655867007151665884261239288523949017916020987120261776470036578396752957177161891596347573660872516590649613560970891983097461740232055140530109097378271209699729595052382346271418437954804304997627153497109703005109744989576251123456901764345916116030104921897501279826650615714933970584537724758491121260095627022560190764835975361963346337675862790412754341728170996318, 36976947455786179964675543426246826400041464134950360524940816372742416810983603131899622852208295331213657060240419632280717580142626256692505119340617350654576814193832152489977338051034158503697165688088667770664774053925309302417311832033020764686933397119750594754870770940102685637455944492400832336960362158899435923937946565751053659624426260414830497719704668015919026550251277555488059097194898226455900742406813891729460880068707648174847929744069568147623377850618169378336283175882630920985800538598954440794846551962319626040597592842674186837634757692558063009735076575277398436924421070555141655930982311657958646557470981614077842371733739463505745067064981227992918836778977224895947161451940821854809466564452214488212824892934863140039512312095480254574533040376312535, 36975160885963102452984251923200234115191359179013544966531422618388826975294859605687403591343995266334193251422862715900565630778681185933708485509546963236997992831135670651299025115872728235289835957838874797967035376891506963137420835505240166306718606399679103718360393628935841578707184416784233649168300147333255755451817193707965563146579177066533375765833757244685760121560101653213325824294782267316374565533490596461935359797599529713739921193636500054312938931564549788626749170778071991253820442458784823385785807470250648242698307526247865980163186411467571656281828066182938779913691242976158494388417872965147474726753852891951839616628525679310700360230984021432540369943935127737710374192781792197577938347413303946690299881145237289268116199437716052467316883436270174, 36968366674459940300559054614940084188374558323392246579167273398599413070865534479824747209451476907318803714383096798332025178971387846698663155808149607958742428220251796107912452133880379770598051564421326288885285540435378298171382729465582684913868701835964557207271476872284543347339173174535734564962677075704701670336758504144228338119092594332750185716741327257162278172804591311643461898742572694557866510576031009513546723752573298339136254253272457970609335855193193351400273689800584159385747999281876734763732561693651768621878737022865948146347170317547272276709869954926940233172842088909262069755282199893275410927053994056361634128992903016200458178395471718282940334322936568626204573401478301121365226280134840720740165168631134123638074121901232924330247495154332254, 36977418407473962230809609334045323898014516834557949297991243165090845304575234555134574296105938349074806994882837267022696222806117046930189851437297010690580732161981446932532691812003001422275232815884021167911564240801249897928068964296163288625804949154130420457030119441442287829091087007790045305094914472681062147843131464076604922609829830083057678675351338026476808418771358077366944250383462906240266647387532208486969174112398349757553742980391705308758971570662048648734690010099240732588129032481724481150503098508826438230601346250986488852778671025618708153965278187864007469645843468495468640356573143948910267807504853429134888718993874237582617354605821812393292178694877192173505841119495227557689578456049869145674623240443503208469133722624612649247341252483150430, 36970629439692117688477262104804559173338211909049933325861513627942289958782619890229607645925775826490596438657204896836196231813824628030850467144745607684254162273199128740310922540381741580878136279647487747727085654647063993473954333869454464515612839197792521402094121076864465379878092641610086335003730311113028454998720667769552793330744179089252777520191536069776056767984799253288063533863114530655633911150198553920428848162147398409990571901266849923536207173856336062843393261903064994686938304157771154497337397290320757367085784944004037140212301247657451574577106477906614465169692827537225161333512301558672638464758842000231109444110605860383337800683371642668162303534027532791464584075855386308627473719720977565403291841636249006410365294379407224010544549054313054, 36970629875864366548049464743356810335351731498279864920424569326187993202767728108903287254995588753920130629407986514230713181886738215635292176525361370064220302506107986178827839081189788144684008308278245740806186000341029034339998241650746650127802904699022581241535031857082516024775825649222319071467782200479860532125286750463493681463185667443972516145289833553750604896087859340949667299864695651447233842645619157573857864205982669407259700142525442835422682564610048693350038219747948357280310505426600586076025252698162597103130936979601690525555224000335490800701710233297711423797724339332684154270457267085257421565184599754160192553736401686925935988678798483378672845574929930562051262529568547310299966542336636326605480103553545862003951070226167696491066382655615582, 36977418846320411731540552953319731428807289750037458256065194815911918373699689499597489706498092907421660521299637475078746389431726485820719290712171121701509328591260985260085416017863970432528358672527488091971989818800427750442654352643321796869972424639892489279828161229083466236162484797518109157028105138679156615521349412172977749574436971323440116656438035412354807469174824402010941165126987937087602802381275804745737842598327788475078766583825914700609895670981223787345081443637810127618968204682494068268429044036471035317788810714679465975301891559419772104726862253449605397144079982924222977192034606534242693000505736556957254647147122480527711805368945889186459020069429556453801784479791829000962488642070014817046902262858802494624551136165765051117072571639970398, 36972888798238313733675843872735162430607956446142917838464627464587438049638802596093799531350239757401258569962068011179783438105336380538175740870127363630299795132057734053471957354308358114108535606031483401976552427158726449542463546206493585409820248041951606907062378705099487446154535430925534195987112397720507976435429557689713389934176951823420637072189044659522802057465981878676253443305126491663424359668011614702746020119769768220280111156678731888485639854281379131891200182409103042823102829010480072192990198746800412900169117897678130406164987035532832365364866713690687556933589306889090757309464936932168344106377848429667998209019234533681810476508008796230315284761167559550074470280548254195476216974805513425250959758795912729453919097162598688181211821994340958, 36972897415739961346244331198306987221409620092348520046033381525552537556413117532209385558880182477329277913499917771897452295981169248241818901353435300459180281207232940799281600525566111113103328170110482943947626629160813513669870821440879680742997413845513837096314827835018540408685500472845827465198230260557252460998223635466222540784458964668648873435968368406455971625345713984905075310789479288631435334926422251389461264184938924127431118941897507996032135906511535210363384924253745245068505238579247895346723140650219952540290159805115230677151649785036662993901747902382472147228349053144318217883296781289073695209673729711376594084736859136629133487375097863739242628312869256662631123610571458322706516403240758070482171462612614253336850244607042996633026134916919902, 36972888794030549257302758716654881522975602845322000526074646211515446967274659839348119749014348312561456542008956864501075028508917984418248154954432771943626288261767408842993499637572593055395712065665417316793900104551508352062187529865554882155403525276706971613165986569237301034677652257936396681768338986461574831917449458967170315733815011753006736722505484407721823253907682053813437743814516305063334949934718898740237955085029131081256141981551544613275417538141174676614616989032718644803172982826630894619108081718237880651655797110385702210769590645164843088135465779576634375427020364673783368264404899063925187217599788855028164070231029140690256960340043633714988871468205328649410452433695393149699552437765167884162694264816435941967964820823233661762141195252986462, 36972896503538395781899251411322937614811370526628597025099638998798385467415956921549667489839792750468646031751019222692604678686145885104684229262891455730125520074886758361039861728330857102734416449218359150169633292675632359533897673836714064872483831859145127456153978413040474909626404424151317081776955896376839778092865746014975706326466706081114674827194453489034140214819728438962055168781756305163988563401082168655544235663591038341245638476364984445654617882051616247627021241326173685678002805833117091948355642217682111401542427034686106593090415649585782578998579951089499396959767390941082330974629387455196507725107954139452072050400823621271718212827440613674444201884642978602000051322514684967414216745864521192950404297021963828325423534135740796536067843295474270, 36977418628230727359820748358099588762190214555555055448866362425742585592586001281667478583892064731133832334368831750372025196910292209778662898037446393247697730148144833094477620808455922713833240778856681144651613065387145240810089334674964301636347406251724669188439566527188589135068007943422518855978080577575186297561373715158420340472557680438618311990182366022435231390617336696168774483735526745763578586061081590719944088959804354483608866335448807440538991926929630605221515779788352209651911504231049555072480538224804807023422519176613923759209804022487722050615302603342070365803796948802922523402510675624416320775428327852512974569166259716090765918254767775494861500470750156861245515506976398366323206560918404605969683582587775144542671532043896395160198802111132254, 36975906877280518019032798659889073674758571127691285246207945840997065605990876741253003358175276544785663511241994501635220943103630236424164906294263477469491833940236699601366834611728763142084619016164044067799133845888113215407891812354786332273516982073258324631033968254796157466558926750262539271899210135829810219656285581417534982092574550250843338665992165916129705666374697191395188040246948408274091403915858585812653828116741485828392974280597712105651805756182964469155502889317741932029632318843333847637472631944464161323607672093393649963916629873895544020454565349395967444239164681565605922094501117867665349330107409872276311388770570192967607227453139170269632114169636273803340882405478224394769636945893983554434324692827502461249949163063395603219120801346417246, 36975905287385495696565854498916585496272026368597319299410048152570533716870872528161197445666387552222924191297415480620820609133757930661623013353592387196707397952189240393176052953793682278089314611800986962142288153061600013704277669936148115437645137160275091328877283120858897951696568947843123184898243719492700285869596522604673464871779154587068862776670909058034223016807826038996070408687586141104561853992288857707105585037456784318251225764132151584135669157506329471393775619016329368495877734182945795773695497039040943684288571837311666779271610286414417257583865920108093058229826204545358884355501576168759876426814859134722792165200010735789287282746291020152335323540358533107991024989146724720316789524165287065779404135998742454178857025171117850372787754065130078, 36975162468061594637511933553363438217796172566936471908671199586874613823250824921015459421220163655799227577876391650138117517469397225354399818643834149813340122338784361394513433402216298330979597725518539651207326153446977403826036150075376076636669919026997136474584997746092135087636088595779180837316154712583716643314205757486864328956720697552668398393353785008253077666619189526312249378771439359633248729369625895671962829936320255920844774853094211211698189183006716504984473591039530165464175533457029935109004201067095611877765666515012916843306601544973776370366092583807679935722863944721231608280476527834633230541938767309201154928120310476992846828304580766684721479411864589035165206076990839073785003361890331286308537007744729631024432241528733693289151893827940958, 36975160885749364125274712223583012346405663830217793121264667598147413607447844402574135816479885447226023207977437025962050279803301910269204931720947389684392620223755129148671550946212467629352454135125775175495499986880903533091611759366914557560212144611369909373284287061119253387017461495914301492301589825770090208009081932955422612618679605375833967727829691614381547289684464619689534930505146372998790641623440418647343459125989209086194731695929138095691881067980227804717998882040868432274195490379954304764177939144052938567043831982876109249240265343684323191318755462703761943333232700048522688606155984968647304432443071157946575008280079285492056670537995743958068815532811250792630548726948164975329292531258054908297514232294071592400733981281282172567607342458401374, 36972897899975755251543879213127293471013673531446976760104391531020038676551331886115411935426492807728577824698592952472422455374921580295651668154422077833405134327600944494382512132230981701354727675213083316501502946696999992345993648662942309914412498452022175829360817763340592191492409526097215763387140139116804629150744038263883703285054111192509430072960270442749474112686734957603712314597275872741153618428110048332186592918118123363881334577979952666636090116787425607467593207619988890859688476637308434220187259461954074906653342586748324135648461854022585395534012001454218478046824449293114405566120112937723645236840337305454770987722267951116491701836056375646497529744184156510600389627227411142622367548119208053359412109496445085222613153817467072966968686513680990, 36972892869434526152768091228904810376828856453149469047517989529268766650769421169867276389327350488765407705580307315771232682322373069424707893426398123675395709938372232385094874010250174087523211310473057388638490230089204148969658897640167955339943019892323009166338282583345782827995460766389906785234371596865517734822854156944488694440062368129351819560346724546881274621984750209795534817485419088032531360016774309760578541867335964521889678691034377816227613166643846308182728743401187608790296651497626047206199535267563885870691226673687688728974608535218289970705753614563510907571519861673326022904092215294720372718702498714740784781452018173718783268554345175447531896989461236092907725645718342153448149909320098396808753143236153034214785158728820481194919070753026654, 36972897897519435287833829135090369014506423992554260038391718580249813158610793714968784899677153624006268096487449850306834528907462959088233781224114135417489924386025397864697425757504335055305562945953389559154935008760411211401297125022873794657052085677750967480968439214837352075927760415058861962526035893112715424742856502458997156101295399614557854321429652971387406118712100865148540619505631268691341230224814833635163060730379926826076817485882815777447926555297048675174176342059271789537185075199313000302040722417548315315965162980683155781341788715943860163704976385453482902561729911017015981510685913015517690296197097981545606124812231477992361437039888421909821283866529093511196147294178285104484744275754988733038159678710992732168830862958416745182783987734737502, 36972896503538395781899251411322937614808402245110937098878827011496902902944502554758700680226664639012248560385327596973389675818220027714601227674060373854200033314645872791685677677592628507203752586396579766599972516333936705566427249304674201489954871843423076602197938948465818554494353415173091409113495992019369064110391537536535216632795940423446290958481450575762244560891712523657588577650607577396183356293632599082558358394258957630690198125758729164119870818795128696543682563310013685541609658099772457147501487809994845294951778258895338215255854294042823537297160191401038683011287546605648988985688963592519790883096717165889554892288100695337920101321502730783017175480269689466867921941398624736673491326241311757391864220386442511696541846021287436746847751859532382, 36970626683154418676127888064287846010366706553694863775673346251400887270381958654959763502782989880089990287074105525194529390200891919484040389988166687934881093895920866528883512183836809195115706945333589037056855696322607691318683415838816437849964121109247213623424775756664463201371630756682749079879197992439070257180376160245189017314593182125129497877351016209422501996347185282400072207918056560763731679267000072555298242061050419188869241302433705404519811579511093745770800603343469224295894499844023756175814180146125003977218314218462479431833100190541638419505472912026543720551446160594094114913666487241616899256095815202085572035504297814646960868169137855796007397728019039191673621490172795650271208958838521522858163150585464595300033997822848765851189216694956638, 36970624409147467047086204709327148041288360289784592544510455511246372708996485543833998210915931716239925497415929412926366365863975831840722350375094548960987820572140078784986831284986309608891078086439495034657963053716953654754097646057261568492845416782744670104495417713918528252918853599656578606964992692100151404789155878090425696257958639376803578255944064619153185744090756950141142273614012029246710151317298968559192352094340850279781689938163146100318887152933796293478455487529954173396868756145471232471783527488094472793598339662147014933513998323859428873506452203890798111072586803350246547459971075701777841946803392852260948643994957309641352950508231807059659334043423711417519590075208687830385348690927232998952417461748352851554269097787320464206797108208136798, 36970635169219147942013105375188155169079148846129430702842883685128070006470163258366250865424955207274248268133709501237948226201164065831003338950668156385750043055314000080463257392604008183327388986654679506391281574221700337644972836478928998272981257804764122502115405926599310937706422916254494142524920759665705909226021203994919030445702605765482906983527877810600039079758236024266459427408127271326845936857237199771079731082852319958703208919345494026849701618496067878164954886872689671244213425742313052896057687877151880616340999131450356826319163021336838115336714540469049722140275619722391361996728561646148473460198356397198877866025122103654299705223056840390222865026502546582173048267530367868116568694471049925405435985941027293338986987926399183975211265376318046, 36975151782473360220951724970420670766199553004585216361577577292761415207178094744530021327194955356348051333797894212457866821343583560502083794973084837649528047834713943145503668508542062876646749617885407886419037392192208078693905050629589380898089440786382840066850402683932604392496440412957445046338020132549306804545003504767956182504109148025912083128656714702088867077405447623289912332203793837713160378055434456252381116655956711659271997298482767766847061562413421187360918509897463760637380688516349855815981062619354504143692759535397703152328061678361005823485803805307342913187805363348809381812952800245688045260968790970863815590585081422472003521490436456316514865959393100872029647498348465636138726424539388843301943732060943013274870022741154455970331293836833374, 36976949043135612081686796829719877263685743169580294378301543558855971951269215630369764003662089333907562184928070097794777370688364408575706734758793673775261840097952785788220975621025292787542868467488022917074172123252264060146986915918778796449366030888627461034176507959150900920503564284853145762074983199104931044042969804697821719071371570904044522758573225735018661668170326453631912949710187219954513717115633364509136250273568663259971482086180538915765703057900714764729811994999821654916380945920097076657069730491973607284254486451076766532507532411899886953282611126869083753442709267442067692316853671537511423827948818791283263627863315302410519889897810476795402058432800941312628418508960253525080033900835764317319730695196885650801977897426241125777821893911573207, 44349395988196178882834224642579322044670122866700260910063882539768863671800578411234791203303216442851316650372938924518946334085775993072295024103565765462710718920645817518261008069569284771290158277833648408729470875185507965439971149919104788572899290196405740591867087079184792779678330920892272702289001733163969641329331161983180883907165561666689826504783402740749118813021716521195193592253139387732107992766779291027517866347431217561121766365417495758052147293562814476500185247754232664142489198818203798383008531195978682118857610028225089201926944974848382125560512614143768140307330548019784255805889310192781453640840046263430883649044239942484432665049857440559107535399059232212213979908300856877545834674632106925460254290245347008770522784146437353466858447935042142, 18490943077870710066716407116961081709221918150355665808075930353943444547812896917211757762411821535546193903957941650965169300952852057334982354189932405330443135870206494337654656599277404163638263307163787000735800781967829981192214298153803102988440726881009832802503116452217158346295314746767434910858617703058543012413844869097479475525856067011969040120536816916967448424718758768816016996781429551636359615260955143331128181694788191106518905756676798215985196931918945764192521292964806317738942307909672757857692958329247178285008416855851923280440853557265302066966071201241469361731116620506720177096844050584520006082661121586668796371252667326005498416766774011879751099936444539076357765732426962978573633229693185724134989982182369602762003589666364767096727508857582174, 44349398257411897837470685772839944894955985627146613035525873473727728507340731074865559389748272427842054695180328186208922152017478009013184524619256294085089003666523843373730728163872375581676427164866883864356011357702979703986891617477919419477815608917120862343955708784773115302507111429750025151860552459151661638193436929711414379927309052841483825480971939281863360454146747822015827489757838310619987615221941499110481558338140276423079940205171857479971293009599832398674769567970780606712202838772239192739915799086394384511475331960041684354645213869550725661234643489692702544738727650592205886735165161537057267237233211706932100380512677927423350646710874233018399719159543806950431251911140723300238272138266152838788356165781731365957071556182591528554829331247067742, 44356197040804497600966446989357932761308306028115215100379725043677535115039987795855173092682488463130147318292248406915839450640663429549391290972984162591930475949283338499640872067109032009637207804118803662422259408967028844329352005743635570084787490141521887496329498666989262613838059072491139097348815623068155311796063546052919366659104583084777856616690950615478319927375464535054959597028699968140738903022649817300098094131458682968994260511451988759900805384437597252345413238053775456143543925602458515451152829206345840151377947162212382875817577534457147775353799953809435479895491435760286048674545014922075788761656056266378452626118217848118680562133849798477218625672993138111342571582493326450566669231496786682799162856098646884699504841806145192532107127111742167, 44356195718391442375887674062182706031137530467595502211658137928483295531036008285867226853856489167729871557840664670764246248751017262408302552525167404811299476650023833925376671118081943649524836775810999457428654198162968401810723886093269987539287864329904316481599387333699036248557498624031417162857589300123320180649062354114918627150281049842661133993740129114977897333841717987210817852271267985554447099777789959180196980706729954693100217632607914571877309411687521714865083922568223730639863496835830524067277161167649946376298589186690938422166243311606134150889053012032852512767882231126396080081331347568848783665819181076269279746594858182640062072490106011678538247679798177673799032259813847907424747217396744018137802181909395931762578922586642316381992085192358494, 36970629439690751721283496110939351436508927102112453675180158242431765546806532518827647159291532326137773745328256773509332659946676930490119485642148759554263693829378026448463113551339047584067648893374865661766507717714798851028848188798619299693976535438491138859141355082114002347732528489857966319023658480334853614905309143992718073305123282153643836680824637463205477747312868788700961573745499148672018908574678771826549779827369522756057899127844472001015636251343197211327256520835954177010130216865450410732016691810570937460810876067991894894157255207317162377154916537441611243707553282415175871414477361253035574738506652724567560509282479613293926845167413435547934264392916725968000205919731288294255669055725068549357027561376493436703869096245901795073993232281170526, 36970629439689552346587408392642405993010529553859266441421246165967515862229720546664856410522161031639659971214504186472335229381670209112109915401621500006291685517252313489426359724744442251239809041986751311922433093324777725100994410734438189869379968865561817564836303672746255217333691137016672806291798787970188102624913051958055386543557980308013942355087478311973652884393215020275848701628083132931505861168303627407571917361108180776248170581232028848255539007779855046388476813863837829553051098747086400104640108455253132884884771960212890021012496990013681083661260773482101584260040629864499011458893318284459483946410938230705694549581631403420582284194417218476098598883968277787066715172010681890864497673605257889169009064600264235591294528807809844895437432105923166, 36970629442145872309521417635430949707066729792523933770983893482239459688997285710487474911723861741631793901721945097291629984089287284171425921577398042627841335190498191824351290700241663145387733496360268239864250209175098780599086302666721286218539660139564764040671404399721988276160016677360039353495044431739390514133390918631644165751348895499200046294949899256138473406456557258755845450327146112153522516100941821039975283510956335149484846504175343897017930858294184856803826388170307090232329929154773682551389961728420475498162600299935092925169964581803242852237477434558395994539622879139680294623271816314016685166512799448461928054101592495113672255439448137598278758460329291878952000889699011192233961798324542222811946405700759329240454814721653886439659115142902366, 36976942427700518621041468442141648115972814556210133675642075450209115637137885055831958875320202492950793110901989622173430922286729456305387393440322104735634279815639858287487186191324002623754841757582019997406462975552598457602517319292588384375912719070683279429447223682081730376389811800869119919294945814939045408346443147769385169050695195091903202280017536713788809317566742971027905005556948563273028677324669672038109979121260985331365033376162882511334029000325138486054021506983610246572370523717920604016936185624005296049722937762583420471783064588267257946364409074440470251385522881477618737380610786381621042134266392060693580246112633925796453060531943017531932905503190102070511927761769791992688719862031076536533044545454189549411699624326068491073125727209962078, 36975155857877337116703010761665503155214557263796661610677640087918238683960687770387588588309805608370173064587373224781485449735009881504295019984285062207573659429237373639646141807201039231401256816649723095673179552157892049807333437925733597627784440489319761935906003491062599590856623444066517587816168719072033249359858779416103360657181877266730943092722375659493715657133655598572900837976006802435222296351913969267718431332812076566078543124978015238442126329577968316790609561600939635714846857753170774205968681264001035365146982118095650653755099394097662547194767976979712822200051255366154736120141274520113635354831304862451245173787716127758782731892306469856182375399009609804348467690598264054501499395739519167600526155058663681161365352352768532850936114440237662]
def wmat : Matrix := fun i j => (Int.ofNat (((packed.getD i 0) >>> (11*j)) % 2048)) - 606
def price : Int := 10029
def literal (input : Nat) (i : Fin 42) : Bool :=
  if i.val<40 then input.testBit i.val else decide (i.val=41)
def positive (r : Nat) := literal (rowInput.getD r 0)
def negative (r : Nat) := literal (colInput.getD r 0)

def cap (v : Fin 42) : Bool :=
  let rs := rows.filter fun i => positive i v
  let cs := cols.filter fun j => !negative j v
  if rs.isEmpty || cs.isEmpty then true else
  if rs.length ≤ cs.length then rs.sublists.all fun a => decide (upper wmat a cs ≤ price)
  else cs.sublists.all fun b => decide (upper (tr wmat) b rs ≤ price)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem capAt0 : cap 0 = true := by decide +kernel
theorem capAt1 : cap 1 = true := by decide +kernel
theorem capAt2 : cap 2 = true := by decide +kernel
theorem capAt3 : cap 3 = true := by decide +kernel
theorem capAt4 : cap 4 = true := by decide +kernel
theorem capAt5 : cap 5 = true := by decide +kernel
theorem capAt6 : cap 6 = true := by decide +kernel
theorem capAt7 : cap 7 = true := by decide +kernel
theorem capAt8 : cap 8 = true := by decide +kernel
theorem capAt9 : cap 9 = true := by decide +kernel
theorem capAt10 : cap 10 = true := by decide +kernel
theorem capAt11 : cap 11 = true := by decide +kernel
theorem capAt12 : cap 12 = true := by decide +kernel
theorem capAt13 : cap 13 = true := by decide +kernel
theorem capAt14 : cap 14 = true := by decide +kernel
theorem capAt15 : cap 15 = true := by decide +kernel
theorem capAt16 : cap 16 = true := by decide +kernel
theorem capAt17 : cap 17 = true := by decide +kernel
theorem capAt18 : cap 18 = true := by decide +kernel
theorem capAt19 : cap 19 = true := by decide +kernel
theorem capAt20 : cap 20 = true := by decide +kernel
theorem capAt21 : cap 21 = true := by decide +kernel
theorem capAt22 : cap 22 = true := by decide +kernel
theorem capAt23 : cap 23 = true := by decide +kernel
theorem capAt24 : cap 24 = true := by decide +kernel
theorem capAt25 : cap 25 = true := by decide +kernel
theorem capAt26 : cap 26 = true := by decide +kernel
theorem capAt27 : cap 27 = true := by decide +kernel
theorem capAt28 : cap 28 = true := by decide +kernel
theorem capAt29 : cap 29 = true := by decide +kernel
theorem capAt30 : cap 30 = true := by decide +kernel
theorem capAt31 : cap 31 = true := by decide +kernel
theorem capAt32 : cap 32 = true := by decide +kernel
theorem capAt33 : cap 33 = true := by decide +kernel
theorem capAt34 : cap 34 = true := by decide +kernel
theorem capAt35 : cap 35 = true := by decide +kernel
theorem capAt36 : cap 36 = true := by decide +kernel
theorem capAt37 : cap 37 = true := by decide +kernel
theorem capAt38 : cap 38 = true := by decide +kernel
theorem capAt39 : cap 39 = true := by decide +kernel
theorem capAt40 : cap 40 = true := by decide +kernel
theorem capAt41 : cap 41 = true := by decide +kernel
theorem caps : ∀ v : Fin 42, cap v = true := by
  intro v
  fin_cases v
  · exact capAt0
  · exact capAt1
  · exact capAt2
  · exact capAt3
  · exact capAt4
  · exact capAt5
  · exact capAt6
  · exact capAt7
  · exact capAt8
  · exact capAt9
  · exact capAt10
  · exact capAt11
  · exact capAt12
  · exact capAt13
  · exact capAt14
  · exact capAt15
  · exact capAt16
  · exact capAt17
  · exact capAt18
  · exact capAt19
  · exact capAt20
  · exact capAt21
  · exact capAt22
  · exact capAt23
  · exact capAt24
  · exact capAt25
  · exact capAt26
  · exact capAt27
  · exact capAt28
  · exact capAt29
  · exact capAt30
  · exact capAt31
  · exact capAt32
  · exact capAt33
  · exact capAt34
  · exact capAt35
  · exact capAt36
  · exact capAt37
  · exact capAt38
  · exact capAt39
  · exact capAt40
  · exact capAt41

theorem literal_bound (v : Fin 42) (a b : List Nat)
    (ha : a.Sublist (rows.filter fun i => positive i v))
    (hb : b.Sublist (cols.filter fun j => !negative j v)) : rect wmat a b ≤ price := by
  have hc := caps v
  dsimp only [cap] at hc
  split at hc
  · rename_i h
    rcases Bool.or_eq_true_iff.mp h with h|h
    · rw [List.isEmpty_iff.mp h] at ha
      have e : a=[] := List.sublist_nil.mp ha
      rw [e,transpose];simp [rect,price]
    · rw [List.isEmpty_iff.mp h] at hb
      have e : b=[] := List.sublist_nil.mp hb
      rw [e];simp [rect,price]
  · split at hc
    · exact (rect_le_upper _ _ hb).trans (decide_eq_true_iff.mp (List.all_eq_true.mp hc _ (List.mem_sublists.mpr ha)))
    · rw [transpose]
      exact (rect_le_upper _ _ ha).trans (decide_eq_true_iff.mp (List.all_eq_true.mp hc _ (List.mem_sublists.mpr hb)))

theorem total : rect wmat rows cols = 975060 := by decide +kernel

def Formula.leaves : Formula → Nat
  | .var _ => 1
  | .conj a b | .disj a b => a.leaves+b.leaves

theorem cost_eq (e : Formula) : e.cost (fun _ => price) = price*(e.leaves:Int) := by
  induction e with
  | var _ => simp [Formula.cost,Formula.leaves]
  | conj a b ih jh | disj a b ih jh => simp [Formula.cost,Formula.leaves,ih,jh,mul_add]

def graph := Simlowker.Graph9840.target
def assignment (r : Nat) (i : Fin 40) := r.testBit i.val
theorem trueRows : ∀ r ∈ rowInput, graph (assignment r)=true := by decide +kernel
theorem falseCols : ∀ r ∈ colInput, graph (assignment r)=false := by decide +kernel
theorem getD_in {xs : List Nat} {i : Nat} (hi : i < xs.length) : xs.getD i 0 ∈ xs := by
  simp [List.getD_eq_getElem?_getD,hi]

theorem lower (e : Formula) (ok : ∀ r, e.eval (literal r)=graph (assignment r)) :
    98 ≤ e.leaves := by
  have h := formula_bound wmat rows cols positive negative (fun _ => price) literal_bound e
    (List.Sublist.refl _) (List.Sublist.refl _)
    (fun i hi => (ok _).trans (trueRows _ (getD_in (List.mem_range.mp hi))))
    (fun j hj => (ok _).trans (falseCols _ (getD_in (List.mem_range.mp hj))))
  rw [total,cost_eq] at h
  unfold price at h
  omega
#print axioms lower
end GraphWeight9840

namespace GraphWeight9840
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def translate : GraphFormula9840.Formula → Formula
  | .var i => .var i
  | .disj l r => .disj (translate l) (translate r)
  | .conj l r => .conj (translate l) (translate r)

theorem translateLeaves (f : GraphFormula9840.Formula) :
    (translate f).leaves=f.leaves := by
  induction f <;> simp_all [translate,Formula.leaves,GraphFormula9840.Formula.leaves]

theorem translateEval (f : GraphFormula9840.Formula) (v : Fin 42 → Bool) :
    (translate f).eval v=f.eval v := by
  induction f <;> simp_all [translate,Formula.eval,GraphFormula9840.Formula.eval]

theorem unrolled_lower (C : Circuit) (hm : Monotone2 C)
    (hc : ∀ x : Fin 40 → Bool,C.eval (List.ofFn x)=Simlowker.Graph9840.target x) :
    98 ≤ (GraphFormula9840.expand C).leaves := by
  rw [← translateLeaves]
  apply lower
  intro r
  have eq : literal r=GraphFormula9840.base (assignment r) := by
    funext i
    by_cases h : i.val<40 <;> simp [literal,GraphFormula9840.base,assignment,h]
  rw [translateEval,eq,GraphFormula9840.expand_eval _ hm]
  exact hc _
#print axioms unrolled_lower
end GraphWeight9840
