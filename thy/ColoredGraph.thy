theory ColoredGraph
imports Main Coloring Permutation
begin

section ‹Colored graphs›

type_synonym vertex = nat

record colored_graph = 
   num_vertices :: nat
   edges :: "(vertex × vertex) set"
   colors :: color_list ― ‹map each vertex to its color›

text ‹Edges and colors are consistent with the fact that the graph has n vertices›
text ‹This is basically an invariant of the colored_graph datatype›
definition n_vertex :: "colored_graph ⇒ bool"  where
  "n_vertex G ⟷ (let n = num_vertices G 
                    in (∀ (v1, v2) ∈ edges G. v1 < n ∧ v2 < n) ∧
                       length (colors G) = n)"

typedef colored_graph_t = "{G :: colored_graph. n_vertex G}"
  by (rule_tac x="⦇num_vertices = 0, edges = {}, colors = []⦈" in exI, simp add: n_vertex_def)


text ‹Check if v is a valid vertex of the graph G›
abbreviation vertex :: "colored_graph ⇒ vertex ⇒ bool" where
  "vertex G v ≡ v < num_vertices G"

lemma edge_vertices [simp]:
  assumes "n_vertex G" "(v1, v2) ∈ edges G"
  shows "vertex G v1" "vertex G v2"
  using assms
  by (metis case_prodD n_vertex_def)+

lemma vertex_perm_fun [simp]:
  assumes "vertex G v" "perm_dom p = num_vertices G"
  shows "vertex G (perm_fun p v)"
  using assms
  by (metis perm_dom_perm_inv perm_fun_perm_inv_range perm_inv_inv)

lemma vertex_perm_fun_inv [simp]:
  assumes "vertex G v" "perm_dom p = num_vertices G"
  shows "vertex G (perm_fun (perm_inv p) v)"
  by (simp add: assms(1) assms(2))

text ‹Coloring function›
abbreviation coloring :: "colored_graph ⇒ color_fun" where
  "coloring G ≡ color_fun (colors G)"

lemma set_all_colors [simp]:
  assumes "n_vertex G"
  shows "set (all_colors (num_vertices G) (coloring G)) = set (colors G)"
  using assms
  unfolding n_vertex_def all_colors_def Let_def
  by (metis color_list_color_fun color_list_def)


text ‹Graph is colored by colors 0, 1, ..., k-1›
definition is_k_colored :: "colored_graph ⇒ nat ⇒ bool" where
  "is_k_colored G k ⟷ set (colors G) = {0..<k}"

lemma all_k_colors:
  assumes "n_vertex G" "is_k_colored G k"
  shows "all_k_colors (num_vertices G) (coloring G)"
  using assms
  unfolding is_k_colored_def all_k_colors_def num_colors_def
  by (metis all_colors_def card_atLeastLessThan color_list_color_fun color_list_def diff_zero n_vertex_def)
 

text ‹Number of colors in a k-colored graph›
definition num_colors :: "colored_graph ⇒ nat" where 
  "num_colors G = (THE k. is_k_colored G k)"

lemma num_colors_k:
  assumes "n_vertex G" "is_k_colored G k"
  shows "num_colors G = k"
  using assms
  unfolding num_colors_def
  by (metis card_atLeastLessThan diff_zero is_k_colored_def the_equality)

lemma num_colors_THE:
  assumes "n_vertex G" "is_k_colored G k"
  shows "(THE k. is_k_colored G k) = k"
  using assms
  by (metis num_colors_k theI_unique)

lemma num_colors_c:
  assumes "n_vertex G" "is_k_colored G k" 
  shows "Coloring.num_colors (num_vertices G) (coloring G) = num_colors G"
  using assms
  unfolding Coloring.num_colors_def all_colors_def num_colors_k[OF assms] is_k_colored_def color_fun_def n_vertex_def Let_def
  by (auto simp add: nth_image)

lemma num_colors_calculate: 
  assumes "n_vertex G" "is_k_colored G k"
  shows "num_colors G = (if num_vertices G = 0 then 0 else Max (set (colors G)) + 1)"
proof (cases "num_vertices G = 0")
  case True
  then show ?thesis
    using assms
    unfolding num_colors_def is_k_colored_def n_vertex_def
    by auto
next
  case False
  then have "k > 0"
    using assms
    unfolding num_colors_def is_k_colored_def n_vertex_def
    by (metis atLeastLessThan0 empty_iff neq0_conv nth_mem)
  hence "k = Suc (Max {0..<k})"
    by (metis (full_types) Max_ge Max_in Suc_lessI Suc_n_not_le_n atLeastLessThan_empty_iff atLeastLessThan_iff finite_atLeastLessThan order_less_imp_le zero_less_Suc)
  then show ?thesis
    using assms False
    by (metis Suc_eq_plus1 is_k_colored_def num_colors_k)
qed

lemma is_k_colored [simp]:
  assumes "n_vertex G" "all_k_colors (num_vertices G) (coloring G)"
  shows "is_k_colored G (num_colors G)"
  using assms
  unfolding all_k_colors_def Coloring.num_colors_def
  by (simp add: is_k_colored_def num_colors_k)
 
text ‹The number of colors is limited by number of vertices›
lemma num_colors_ub:
  assumes "n_vertex G" "is_k_colored G k"
  shows "num_colors G ≤ num_vertices G"
  using assms num_colors_k[OF assms]
  by (metis card_atLeastLessThan card_length diff_zero is_k_colored_def n_vertex_def)


text ‹Recolor graph by the given coloring›

definition recolor :: "colored_graph ⇒ color_fun ⇒ colored_graph" where
  "recolor G π = G ⦇ colors := color_list (num_vertices G) π ⦈"

lemma num_vertices_recolor [simp]:
  shows "num_vertices (recolor G π) = num_vertices G"
  by (simp add: recolor_def)


lemma n_vertex_recolor [simp]:
  assumes "n_vertex G"
  shows "n_vertex (recolor G π)"
  using assms
  unfolding recolor_def n_vertex_def Let_def
  by (auto simp add: color_list_def)

lemma coloring_recolor [simp]:
  assumes "n_vertex G" "vertex G v" 
  shows "coloring (recolor G π) v = π v"
  using assms
  unfolding n_vertex_def Let_def recolor_def color_fun_def color_list_def
  by simp

lemma cells_coloring_recolor [simp]:
  assumes "n_vertex G"
  shows "cells (num_vertices G) (coloring (recolor G π)) = cells (num_vertices G) π"
  by (metis (no_types, lifting) assms cells_coloring_color_list color_list_color_fun color_list_def ext_inject length_map n_vertex_def recolor_def surjective update_convs(3))

lemma num_colors_recolor:
  assumes "n_vertex G" "all_k_colors (num_vertices G) π"
  shows "num_colors (recolor G π) = Coloring.num_colors (num_vertices G) π"
proof (rule num_colors_k)
  show "n_vertex (recolor G π)"
    by (simp add: assms(1))
next
  show "is_k_colored (recolor G π) (Coloring.num_colors (num_vertices G) π)"
    using ‹all_k_colors (num_vertices G) π› 
    unfolding is_k_colored_def recolor_def color_list_def all_k_colors_def all_colors_def
    by simp
qed

lemma all_k_colors_recolor:
  assumes "n_vertex G" "all_k_colors (num_vertices G) c"
  shows "all_k_colors (num_vertices G) (coloring (recolor G c))"
  using assms 
  by (auto simp add: all_k_colors_def Coloring.num_colors_def all_colors_def)


text‹The effect of vertices perm on edges›
definition perm_edges :: "perm ⇒ (nat × nat) set ⇒ (nat × nat) set" where
  "perm_edges p es = (perm_fun_pair p) ` es" 

lemma perm_edges_perm_id' [simp]:
  assumes "∀ (x, y) ∈ es. x < n ∧ y < n"
  shows "perm_edges (perm_id n) es = es" 
  using assms
  unfolding perm_edges_def
  by force

lemma perm_edges_perm_id [simp]:
  assumes "n_vertex G"
  shows "perm_edges (perm_id (num_vertices G)) (edges G) = edges G" 
  by (meson assms n_vertex_def perm_edges_perm_id')

lemma perm_edges_perm_comp [simp]:
  assumes "n_vertex G" 
          "perm_dom p1 = (num_vertices G)" "perm_dom p2 = (num_vertices G)"
  shows "perm_edges (perm_comp p1 p2) (edges G) = 
         perm_edges p1 (perm_edges p2 (edges G))"
  using assms
  unfolding perm_edges_def n_vertex_def Let_def
  by force

text ‹The effect of vertices perm on the colored graph›
definition perm_graph :: "perm ⇒ colored_graph ⇒ colored_graph" where
  "perm_graph p G = 
   ⦇
      num_vertices = num_vertices G,
      edges = perm_edges p (edges G),
      colors = color_list (num_vertices G) (perm_coloring p (coloring G))
   ⦈"

lemma perm_graph_num_vertices [simp]:
  shows "num_vertices (perm_graph p G) = num_vertices G"
  by (simp add: perm_graph_def)

lemma perm_graph_edges [simp]:
  shows "edges (perm_graph p G) = perm_edges p (edges G)"
  by (simp add: perm_graph_def)

lemma perm_graph_colors [simp]:
  assumes "perm_dom p = num_vertices G" "n_vertex G"
  shows "colors (perm_graph p G) = perm_reorder p (colors G)"
proof-
  have "length (colors G) = num_vertices G"
    by (meson assms(2) n_vertex_def)
  then have "colors (perm_graph p G) =
        map (λ k. colors G ! k) (perm_fun_list (perm_inv p) [0..<num_vertices G])"
    using assms
    by (auto simp add: perm_graph_def color_list_def perm_coloring_def color_fun_def perm_fun_list_def)
  then show ?thesis
    using assms perm_reorder
    by (metis ‹length (colors G) = num_vertices G› perm_inv_perm_list)
qed

lemma perm_graph_coloring_perm_node [simp]:
  assumes "vertex G v" "perm_dom p = num_vertices G"
  shows "coloring (perm_graph p G) (perm_fun p v) = coloring G v"
  using assms
  by (auto simp add: perm_graph_def color_list_def)
  

lemma perm_graph_coloring [simp]:
  assumes "perm_dom p = num_vertices g"
  shows "color_list (num_vertices g) (coloring (perm_graph p g)) = 
         color_list (num_vertices g) (perm_coloring p (coloring g))"
  by (simp add: color_list_eq perm_graph_def color_list_def)

lemma perm_edges_join_vertices:
  assumes "perm_dom p = num_vertices G" "n_vertex G" 
          "(v1, v2) ∈ perm_edges p (edges G)"
  shows "vertex G v1" "vertex G v2"
  using assms
  unfolding perm_edges_def
  by auto

lemma perm_graph_n_vertex [simp]:
  assumes "perm_dom p = num_vertices G" "n_vertex G"
  shows "n_vertex (perm_graph p G)"
  using assms
  unfolding n_vertex_def perm_graph_def Let_def
  using assms(2) case_prodI2 color_list_def length_map perm_edges_join_vertices
  by auto

lemma perm_graph_perm_comp [simp]:
  assumes "n_vertex G"
          "perm_dom p1 = num_vertices G" "perm_dom p2 = num_vertices G"
  shows "perm_graph (perm_comp p1 p2) G = perm_graph p1 (perm_graph p2 G)"
  using assms
  unfolding perm_graph_def
  by (auto simp add: color_list_eq perm_coloring_def color_list_def)

lemma perm_graph_perm_inv1 [simp]: 
  assumes "n_vertex G" "perm_dom p = num_vertices G"
  shows "perm_graph (perm_inv p) (perm_graph p G) = G"
  using assms
  by (metis (full_types) color_fun_def color_list_perm_coloring_perm_id n_vertex_def old.unit.exhaust perm_comp_perm_inv1 perm_dom_perm_inv perm_edges_perm_id perm_graph_def perm_graph_perm_comp surjective)

lemma perm_graph_perm_inv2 [simp]: 
  assumes "n_vertex G" "perm_dom p = num_vertices G"
  shows "perm_graph p (perm_graph (perm_inv p) G) = G"
  using assms
  by (metis perm_dom_perm_inv perm_graph_perm_inv1 perm_inv_inv)

lemma perm_graph_perm_id [simp]:
  assumes "n_vertex G"
  shows "perm_graph (perm_id (num_vertices G)) G = G"
  using assms
  unfolding perm_graph_def 
  by (metis (full_types) color_fun_def color_list_perm_coloring_perm_id n_vertex_def old.unit.exhaust perm_edges_perm_id surjective)

lemma is_k_colored_perm_graph [simp]:
  assumes "n_vertex G" "perm_dom p = num_vertices G"
  assumes "is_k_colored G (num_colors G)"
  shows "is_k_colored (perm_graph p G) (num_colors G)"
  by (metis (no_types, lifting) assms is_k_colored_def list.set_map map_nth n_vertex_def perm_dom_perm_inv perm_graph_colors perm_list_set perm_reorder set_upt)

lemma num_colors_perm_graph [simp]:
  assumes "n_vertex G" "all_k_colors (num_vertices G) (coloring G)" "perm_dom p = num_vertices G"
  shows "num_colors (perm_graph p G) = num_colors G"
proof-
  have "is_k_colored G (num_colors G)"
    by (metis (no_types, lifting) all_colors_def all_k_colors_def assms(1) assms(2) color_list_color_fun color_list_def is_k_colored_def n_vertex_def num_colors_k)
  then have "is_k_colored (perm_graph p G) (num_colors G)"
    using assms
    by simp
  thus ?thesis
    using assms(1) assms(3) num_colors_k perm_graph_n_vertex 
    by blast
qed

lemma cells_perm_graph:
  assumes "perm_dom p = num_vertices G" "n_vertex G"
  shows "cells (num_vertices (perm_graph p G)) (coloring (perm_graph p G)) =
         map (perm_fun_set p) (cells (num_vertices G) (coloring G))"
proof-
  have "cells (num_vertices (perm_graph p G)) (coloring (perm_graph p G)) =
        cells (num_vertices G) (perm_coloring p (coloring G))"
    by (metis assms(1) cells_coloring_color_list perm_graph_coloring perm_graph_num_vertices)
  then show ?thesis
    by (simp add: assms(1))
qed

end