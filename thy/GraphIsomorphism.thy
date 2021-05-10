theory GraphIsomorphism
  imports Main Coloring Permutation "HOL-Library.FSet" "HOL-Library.List_Lexorder"
begin

section \<open>Colored graphs\<close>

record colored_graph = 
   num_vertices :: nat
   edges :: "(nat \<times> nat) set"
   colors :: "nat list" \<comment> \<open>map each vertex to its color\<close>

text \<open>Edges and colors are consistent with the fact that the graph has n vertices\<close>
text \<open>This is basically an invariant of the colored_graph datatype\<close>
definition n_vertex :: "colored_graph \<Rightarrow> bool"  where
  "n_vertex G \<longleftrightarrow> (let n = num_vertices G 
                    in (\<forall> (v1, v2) \<in> edges G. v1 < n \<and> v2 < n) \<and>
                       length (colors G) = n)"

text \<open>Check if v is a valid vertex of the graph G\<close>
abbreviation vertex :: "colored_graph \<Rightarrow> nat \<Rightarrow> bool" where
  "vertex G v \<equiv> v < num_vertices G"

text \<open>Coloring function\<close>
definition coloring :: "colored_graph \<Rightarrow> coloring" where
  "coloring G = (\<lambda> v. (if vertex G v then (colors G) ! v else undefined))"

lemma coloring_lt [simp]:
  assumes "vertex G v"
  shows "coloring G v = colors G ! v"
  using assms
  by transfer (simp add: coloring_def)

text \<open>Recolor graph by the given coloring\<close>

definition recolor :: "colored_graph \<Rightarrow> coloring \<Rightarrow> colored_graph" where
  "recolor G \<pi> = G \<lparr> colors := color_list (num_vertices G) \<pi> \<rparr>"

lemma coloring_recolor [simp]:
  assumes "vertex G v" 
  shows "coloring (recolor G \<pi>) v = \<pi> v"
  using assms
  unfolding coloring_def recolor_def color_list_def
  by auto

text \<open>Graph is colored by colors 0, 1, ..., k-1\<close>
definition is_k_colored :: "colored_graph \<Rightarrow> nat \<Rightarrow> bool" where
  "is_k_colored G k \<longleftrightarrow> set (colors G) = {0..<k}"

text \<open>Number of colors in a k-colored graph\<close>
definition num_colors :: "colored_graph \<Rightarrow> nat" where 
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

lemma num_colors: 
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

text \<open>The number of colors is limited by number of vertices\<close>
lemma num_colors_ub:
  assumes "n_vertex G" "is_k_colored G k"
  shows "num_colors G \<le> num_vertices G"
  using assms num_colors_k[OF assms]
  by (metis card_atLeastLessThan card_length diff_zero is_k_colored_def n_vertex_def)

lemma num_colors_c:
  assumes "n_vertex G" "is_k_colored G k" 
  shows "Coloring.num_colors (num_vertices G) (coloring G) = num_colors G"
  using assms
  unfolding Coloring.num_colors_def all_colors_def num_colors_k[OF assms] is_k_colored_def coloring_def n_vertex_def Let_def
  by (auto simp add: nth_image)


lemma consecutive:
  assumes "n_vertex G" "is_k_colored G k"
  shows "consecutive (num_vertices G) (coloring G)"
proof -
  have "all_colors (num_vertices G) (coloring G) = {0..<num_colors G}"
    by (metis (no_types, lifting) all_colors_def assms(1) assms(2) atLeastLessThan_iff coloring_lt image_cong is_k_colored_def n_vertex_def nth_image num_colors_k order_refl take_all)
  thus ?thesis
    using num_colors_c[OF assms]
    unfolding consecutive_def
    by simp
qed


text\<open>The effect of vertices perm on edges\<close>
definition perm_edges :: "perm \<Rightarrow> (nat \<times> nat) set \<Rightarrow> (nat \<times> nat) set" where
  "perm_edges p es = 
       (let pf = perm_fun p 
         in (\<lambda> (v1, v2). (pf v1, pf v2)) ` es)"
                                                                      
text\<open>The effect of vertices perm on colors\<close>
definition perm_coloring :: "perm \<Rightarrow> coloring \<Rightarrow> coloring" where
  "perm_coloring p coloring_fun = coloring_fun \<circ> (perm_fun (perm_inv p))"

text \<open>The effect of vertices perm on the colored graph\<close>
definition perm_graph :: "perm \<Rightarrow> colored_graph \<Rightarrow> colored_graph" where
  "perm_graph p G = 
   \<lparr>
      num_vertices = num_vertices G,
      edges = perm_edges p (edges G),
      colors = color_list (num_vertices G) (perm_coloring p (coloring G))
   \<rparr>"

lemma num_vertices_perm_graph [simp]:
  shows "num_vertices (perm_graph p G) = num_vertices G"
  by (simp add: perm_graph_def)

lemma colors_perm_graph:
  assumes "perm_dom p = num_vertices G" "n_vertex G"
  shows "colors (perm_graph p G) = 
         map (\<lambda> k. colors G ! k) (perm_list (perm_inv p))"
proof-
  have "\<forall> v. vertex G v \<longrightarrow> vertex G (perm_fun (perm_inv p) v)"
    by (simp add: assms(1) perm_fun_perm_inv_range)
  then have "colors (perm_graph p G) =
             map (\<lambda> k. colors G ! k) (perm_fun_list (perm_inv p) [0..<num_vertices G])"
    using assms
    by (auto simp add: perm_graph_def color_list_def perm_coloring_def coloring_def perm_fun_list_def)

  moreover

  have "perm_fun_list (perm_inv p) [0..<perm_dom p] = perm_list (perm_inv p)"
    unfolding perm_fun_list_def
    by transfer (auto simp add: perm_fun'_def perm_inv'_def)

  ultimately 
  
  show ?thesis
    using assms
    by auto
qed

lemma coloring_perm_graph_permute_node:
  assumes "vertex G v" "perm_dom p = num_vertices G"
  shows "coloring (perm_graph p G) (perm_fun p v) = coloring G v"
proof-
  have "vertex G (perm_fun p v)"
    by (metis assms(1) assms(2) perm_dom_perm_inv perm_fun_perm_inv_range perm_inv_inv)
  then show ?thesis
    using assms perm_fun_perm_inv2[of p "num_vertices G"] assms
    unfolding perm_graph_def
    by (auto simp add: color_list_def perm_coloring_def coloring_def)
qed

lemma coloring_perm_graph:
  assumes "perm_dom p = num_vertices g"
  shows "color_list (num_vertices g) (coloring (perm_graph p g)) = 
         color_list (num_vertices g) (perm_coloring p (coloring g))"
  by (smt (verit, best) assms color_list_eq coloring_perm_graph_permute_node comp_def perm_fun_perm_inv1 perm_fun_perm_inv_range perm_coloring_def)

lemma perm_graph_perm_comp:
  assumes "perm_dom p1 = num_vertices G" "perm_dom p2 = num_vertices G" "n_vertex G"
  shows "perm_graph p1 (perm_graph p2 G) = perm_graph (perm_comp p1 p2) G"
  using assms
proof-
  have "perm_edges p1 (perm_edges p2 (edges G)) = perm_edges (perm_comp p1 p2) (edges G)"
    using \<open>n_vertex G\<close>
    unfolding n_vertex_def perm_edges_def Let_def
    by (smt (z3) assms(1) assms(2) case_prodE comp_apply image_cong image_image old.prod.case perm_fun_perm_comp)
  moreover
  have "\<forall> v. vertex G v \<longrightarrow> (perm_coloring p1 (perm_coloring p2 (coloring G))) v = 
        (perm_coloring (perm_comp p1 p2) (coloring G)) v"
  proof safe
    fix v
    assume "vertex G v"
    have "(perm_fun (perm_inv p2) \<circ> perm_fun (perm_inv p1)) v =
          (perm_fun (perm_inv (perm_comp p1 p2))) v"
    proof-
      have "(perm_fun (perm_inv p2) \<circ> perm_fun (perm_inv p1)) v = 
            perm_fun (perm_comp (perm_inv p2) (perm_inv p1)) v"
        using \<open>vertex G v\<close> assms
        using perm_fun_perm_comp[of "perm_inv p2" "num_vertices G" "perm_inv p1"]
        by auto
      also have "... = perm_fun (perm_inv (perm_comp p1 p2)) v"
        by (simp add: assms(1) assms(2) perm_inv_perm_comp)
      finally show ?thesis
        by simp
    qed
    then show "perm_coloring p1 (perm_coloring p2 (coloring G)) v =
          perm_coloring (perm_comp p1 p2) (coloring G) v "
      unfolding perm_coloring_def
      by auto
  qed
  ultimately
  show ?thesis
    unfolding perm_graph_def
    by (smt (z3) assms(1) assms(2) atLeast0LessThan color_list_def coloring_perm_graph comp_def lessThan_iff map_eq_conv perm_fun_perm_inv_range perm_coloring_def perm_graph_def select_convs(1) select_convs(2) set_upt)
qed

lemma perm_graph_permute_id:
  assumes "n_vertex G"
  shows "perm_graph (perm_id n) G = G"
  using assms
  sorry



definition is_isomorphism :: "perm \<Rightarrow> colored_graph \<Rightarrow> colored_graph \<Rightarrow> bool" where
  "is_isomorphism p G1 G2 \<longleftrightarrow> 
      perm_dom p = num_vertices G1 \<and> 
      perm_graph p G1 = G2"

definition isomorphic :: "colored_graph \<Rightarrow> colored_graph \<Rightarrow> bool" (infixl "\<simeq>" 100) where
  "isomorphic G1 G2 \<longleftrightarrow> (\<exists> p. is_isomorphism p G1 G2)"

lemma isomorphic_num_vertices:
  assumes "isomorphic G1 G2"
  shows "num_vertices G1 = num_vertices G2"
  using assms
  by (metis is_isomorphism_def isomorphic_def perm_graph_def select_convs(1))

lemma isomorphic_num_edges:
  assumes "isomorphic G1 G2" "n_vertex G1"
  shows "card (edges G1) = card (edges G2)"
proof-
  from assms obtain p where p: "perm_dom p = num_vertices G1" "perm_graph p G1 = G2"
    unfolding isomorphic_def is_isomorphism_def 
    by auto
  let ?f = "(\<lambda> (v1, v2). (perm_fun p v1, perm_fun p v2))"
  have "inj_on ?f (edges G1)"
    unfolding inj_on_def
  proof safe
    fix v1 v2 v1' v2'
    assume *: "(v1, v2) \<in> edges G1" "(v1', v2') \<in> edges G1" 
      "perm_fun p v1 = perm_fun p v1'"
      "perm_fun p v2 = perm_fun p v2'"
    let ?n = "num_vertices G1"
    have "v1 < ?n" "v2 < ?n" "v1' < ?n" "v2' < ?n"
      using \<open>n_vertex G1\<close> *(1-2)
      unfolding n_vertex_def Let_def 
      by auto
    then show "v1 = v1'" "v2 = v2'"
      using p(1) * is_perm_fun[of p]
      unfolding is_perm_fun_def bij_betw_def inj_on_def
      by auto
  qed
  then show ?thesis
    using p
    unfolding perm_graph_def perm_edges_def Let_def
    by (auto simp add: card_image)
qed

lemma isomorphic_n_vertex:
  assumes "isomorphic G1 G2" "n_vertex G1"
  shows "n_vertex G2"
proof-
  from assms obtain p where p: "perm_dom p = num_vertices G1" "perm_graph p G1 = G2"
    unfolding isomorphic_def is_isomorphism_def 
    by auto
  let ?f = "(\<lambda> (v1, v2). (perm_fun p v1, perm_fun p v2))" and ?n = "num_vertices G1"
  have pf: "\<forall> v < ?n. perm_fun p v < ?n"
    using p(1) is_perm_fun[of p]
    unfolding is_perm_fun_def bij_betw_def
    by auto
  show ?thesis
    using p pf \<open>n_vertex G1\<close>
    unfolding n_vertex_def Let_def perm_graph_def perm_edges_def color_list_def
    using diff_zero by force
qed


lemma isomorphic_k_colored:
  assumes "isomorphic G1 G2" "n_vertex G1" "is_k_colored G1 k"
  shows "is_k_colored G2 k"
proof-
  from assms obtain p where p: "perm_dom p = num_vertices G1" "perm_graph p G1 = G2"
    unfolding isomorphic_def is_isomorphism_def 
    by auto
  have 1: "\<forall> v. vertex G1 v \<longrightarrow> coloring G1 v < k"
    using assms(2-3)
    unfolding n_vertex_def is_k_colored_def Let_def
    by auto

  have 2: "\<forall> c < k. \<exists> v. vertex G1 v \<and> coloring G1 v = c"
    using assms(2-3)
    unfolding n_vertex_def is_k_colored_def Let_def coloring_def
    by (metis atLeast0LessThan in_set_conv_nth lessThan_iff)

  have 3: "\<forall> v. vertex G1 v \<longrightarrow> vertex G1 (perm_fun p v)"
    using \<open>n_vertex G1\<close> is_perm_fun[of p] p(1)
    unfolding n_vertex_def is_perm_fun_def bij_betw_def Let_def
    by auto

  have 4: "\<forall> v. vertex G1 v \<longrightarrow> (\<exists> v'. vertex G1 v' \<and> perm_fun p v' = v)"
    using \<open>n_vertex G1\<close> is_perm_fun[of p] p(1)
    unfolding n_vertex_def is_perm_fun_def bij_betw_def Let_def
    by (metis (mono_tags, lifting) atLeast0LessThan image_iff lessThan_iff)

  show ?thesis
    unfolding is_k_colored_def
  proof safe
    fix x
    assume "x \<in> set (colors G2)"
    then show "x \<in> {0..<k}"
      using p 1 3 colors_perm_graph[of p G1] \<open>n_vertex G1\<close>
      by auto
  next
    fix c
    assume "c \<in> {0..<k}"
    hence "c < k"
      by auto
    then obtain v where "vertex G1 v" "coloring G1 v = c"
      using 2
      by auto
    moreover
    obtain v' where "vertex G1 v'" "perm_fun p v' = v"
      using 4 \<open>vertex G1 v\<close>
      by auto
    ultimately
    show "c \<in> set (colors G2)"
      using p colors_perm_graph[of p G1] \<open>n_vertex G1\<close>
      by auto
  qed
qed

definition is_automorphism :: "colored_graph \<Rightarrow> perm \<Rightarrow> bool" where
  "is_automorphism G p \<longleftrightarrow> is_isomorphism p G G"

definition automorphisms :: "colored_graph \<Rightarrow> perm set" where
  "automorphisms G = {p. is_automorphism G p}"

lemma coloring_permute_node_automorphism:
  assumes "is_automorphism G p" "vertex G v"
  shows "(coloring G) v = (coloring G) (perm_fun p v)"
  using assms
  unfolding is_automorphism_def is_isomorphism_def
  by (metis coloring_perm_graph_permute_node)

definition is_canon_form :: "(colored_graph \<Rightarrow> colored_graph) \<Rightarrow> bool" where
  "is_canon_form C \<longleftrightarrow> 
   (\<forall> G. n_vertex G \<longrightarrow> G \<simeq> C G \<and> 
         (\<forall> p. perm_dom p = num_vertices G \<longrightarrow> C (perm_graph p G) = C G))"

lemma isomorphic_same_canon_form:
  assumes "is_canon_form C" "n_vertex G" "n_vertex G'"
  shows "G \<simeq> G' \<longleftrightarrow> C G = C G'"
proof
  assume "G \<simeq> G'"
  then show "C G = C G'"
    using assms
    unfolding is_canon_form_def isomorphic_def
    by (metis is_isomorphism_def)
next
  assume "C G = C G'"
  then show "G \<simeq> G'"
    using assms
    unfolding is_canon_form_def isomorphic_def is_isomorphism_def
    sorry
qed

type_synonym vertex_list = "nat list" 

abbreviation is_vertex_list :: "colored_graph \<Rightarrow> vertex_list \<Rightarrow> bool" where
 "is_vertex_list G V \<equiv> distinct V \<and> set V \<subseteq> {0..<num_vertices G}"

locale refinement_function =
  fixes \<R> :: "colored_graph \<Rightarrow> vertex_list \<Rightarrow> coloring"
  assumes \<R>_finer: 
    "\<And> V G. is_vertex_list G V \<Longrightarrow> 
               finer (num_vertices G) (\<R> G V) (coloring G)"
  assumes \<R>_cells:
    "\<And> V G. \<lbrakk>is_vertex_list G V; v \<in> set V\<rbrakk> \<Longrightarrow> 
               {v} \<in> set (cells (num_vertices G) (\<R> G V))"
  assumes \<R>_perm:
    "\<And> V G p v. \<lbrakk>is_vertex_list G V; 
                 perm_dom p = num_vertices G;
                 vertex G v\<rbrakk> \<Longrightarrow> 
                   (\<R> (perm_graph p g) (perm_fun_list p V)) v = 
                   (perm_coloring p (\<R> g V)) v"
begin

lemma \<R>_perm_perm:
  assumes "vertex G v" "is_vertex_list G V" "perm_dom p = num_vertices G"
  shows "\<R> (perm_graph p G) (perm_fun_list p V) (perm_fun p v) = \<R> G V v"
proof (subst \<R>_perm)
  show "vertex G (perm_fun p v)"
    by (metis assms(1) assms(3) perm_dom_perm_inv perm_fun_perm_inv_range perm_inv_inv)
next
  show "perm_coloring p (\<R> G V) (perm_fun p v) = \<R> G V v"
    unfolding perm_coloring_def
    using assms(1) assms(3) perm_fun_perm_inv2 by auto
qed (simp_all add: assms)

end

locale target_cell_selector = refinement_function + 
  fixes \<T> :: "colored_graph \<Rightarrow> vertex_list \<Rightarrow> nat fset"
  assumes \<T>_discrete: 
    "\<And> V G. \<lbrakk>is_vertex_list G V; 
             is_discrete_coloring (num_vertices G) (\<R> G V)\<rbrakk> \<Longrightarrow> 
               \<T> G V =  {||}"
  assumes \<T>_non_discrete:
    "\<And> V G. \<lbrakk>is_vertex_list G V;
              \<not> is_discrete_coloring (num_vertices G) (\<R> G V)\<rbrakk> \<Longrightarrow> 
               fset (\<T> G V) \<in> set (cells (num_vertices G) (\<R> G V)) \<and> 
               fcard (\<T> G V) > 1"
  assumes \<T>_perm:
    "\<And> V G p. \<lbrakk>is_vertex_list G V; 
               perm_dom p = num_vertices G\<rbrakk> \<Longrightarrow> 
                 \<T> (perm_graph p G) (perm_fun_list p V) = perm_fun_fset p (\<T> G V)"
begin

lemma is_vertex_list_T_extend:
  assumes "is_vertex_list G V" "v' \<in> fset (\<T> G V)"
  shows "is_vertex_list G (v' # V)"
proof-
  have "vertex G v'"
  proof-
    have "\<not> is_discrete_coloring (num_vertices G) (\<R> G V)"
      using \<T>_discrete[OF assms(1)] assms(2)
      by auto
    then have "fset (\<T> G V) \<in> set (cells (num_vertices G) (\<R> G V))"
      using \<T>_non_discrete[OF assms(1)]
      by auto
    then obtain c where "c < Coloring.num_colors (num_vertices G) (\<R> G V)"
                        "v' \<in> cell (num_vertices G) (\<R> G V) c"
      using \<open>v' \<in> fset (\<T> G V)\<close>
      unfolding cells_def
      by auto
    thus ?thesis
      unfolding cell_def
      by auto
  qed

  moreover

  have "v' \<notin> set V"
  proof (rule ccontr)
    assume "\<not> ?thesis"
    then have "{v'} \<in> set (cells (num_vertices G) (\<R> G V))"
      using \<R>_cells[OF assms(1)]
      by simp
    have "\<not> is_discrete_coloring (num_vertices G) (\<R> G V)"
      using \<T>_discrete[OF assms(1)] assms(2)
      by auto
    then have "fset (\<T> G V) \<in> set (cells (num_vertices G) (\<R> G V))" 
              "fcard (\<T> G V) > 1"
      using \<T>_non_discrete[OF assms(1)]
      by auto
    have "{v'} = fset (\<T> G V)"
      using cells_disjunct
      using \<open>fset (\<T> G V) \<in> set (cells (num_vertices G) (\<R> G V))\<close> \<open>{v'} \<in> set (cells (num_vertices G) (\<R> G V))\<close> assms(2)
      by blast
    then show False
      using `fcard (\<T> G V) > 1`
      by (metis One_nat_def card.empty card.insert empty_iff fcard.rep_eq finite.intros(1) neq_iff)
  qed

  ultimately

  show ?thesis
    using \<open>is_vertex_list G V\<close>
    by auto
qed

text \<open>Data structure for representing search tree\<close>
datatype Tree = Node "vertex_list" "Tree fset"

primrec nodes :: "Tree \<Rightarrow> vertex_list set" where
  "nodes (Node V ns) = {V} \<union> (\<Union> (fset (nodes |`| ns)))"

primrec leaves :: "colored_graph \<Rightarrow> Tree \<Rightarrow> vertex_list set" where
  "leaves G (Node V ns) = 
       (if \<T> G V = {||} then
           {V}
        else
           (\<Union> (fset (leaves G |`| ns))))"

lemma leaves_are_nodes: "leaves G T \<subseteq> nodes T"
  by (induction T) auto

text \<open>Function that creates the search tree from the given graph\<close>
function expand_tree :: "colored_graph \<Rightarrow> nat list \<Rightarrow> Tree" where
  "expand_tree G V = 
     (if \<T> G V = {||} then 
         Node V {||} 
      else
         Node V ((\<lambda> v. expand_tree G (v # V)) |`| (\<T> G V)))"
  by pat_completeness auto
termination sorry

declare expand_tree.simps[simp del]

definition tree :: "colored_graph \<Rightarrow> Tree" where
  "tree G = expand_tree G []"

lemma V_in_nodes [simp]:
  shows "V \<in> nodes (expand_tree G V)"
  by (simp add: expand_tree.simps[of G V])

text \<open>Tree contains only vertex lists\<close>
lemma expand_tree_is_vertex_list:
  assumes "is_vertex_list G V" "V' \<in> nodes (expand_tree G V)"
  shows "is_vertex_list G V'"
  using assms
proof (induction G V rule: expand_tree.induct)
  case (1 G V)
  show ?case
  proof (cases "\<T> G V = {||}")
    case True
    then show ?thesis
      using expand_tree.simps[of G V] 1(2) 1(3)
      by auto
  next
    case False
    then show ?thesis
      using expand_tree.simps[of G V] 1 is_vertex_list_T_extend
      by auto
  qed
qed

lemma tree_is_vertex_list:
  assumes "V \<in> nodes (tree g)"
  shows "is_vertex_list g V"
  by (metis assms atLeastLessThan0 distinct.simps(1) empty_set expand_tree_is_vertex_list ivl_subset le_numeral_extra(3) tree_def)


lemma leaves_iff_discrete_expand_tree:
  assumes "is_vertex_list G V" 
  shows "V' \<in> leaves G (expand_tree G V) \<longleftrightarrow> 
           V' \<in> nodes (expand_tree G V) \<and>
           is_discrete_coloring (num_vertices G) (\<R> G V')"
  using assms
proof (induction G V rule: expand_tree.induct)
  case (1 G V)
  show ?case
  proof (cases "\<T> G V = {||}")
    case True
    thus ?thesis
      using \<T>_non_discrete[of V G] 1(2) expand_tree.simps[of G V]
      by (auto simp add: fcard_fempty gr_implies_not0)
  next
    case False
    have *: "\<forall> z \<in> fset (\<T> G V). is_vertex_list G (z # V)"
      by (metis "1.prems" is_vertex_list_T_extend)
    let ?f = "(\<lambda>v. expand_tree G (v # V))"
    have "V' \<in> leaves G (Node V (?f |`| \<T> G V)) \<longleftrightarrow>
         (V' \<in> nodes (Node V (?f |`| \<T> G V)) \<and>
         is_discrete_coloring (num_vertices G) (\<R> G V'))"
      using * 1(1)[OF False] 1(2) False \<T>_discrete
      by auto
    then show ?thesis
      using False
      by (simp add: expand_tree.simps[of G V])
  qed
qed

lemma leaves_iff_discrete:
  shows "V' \<in> leaves G (tree G) \<longleftrightarrow> 
           V' \<in> nodes (tree G) \<and>
           is_discrete_coloring (num_vertices G) (\<R> G V')"
  by (simp add: leaves_iff_discrete_expand_tree tree_def)

lemma leaves_of_node:
  assumes "V1' \<in> leaves G (expand_tree G V1)" "V1 \<in> nodes (expand_tree G V0)"
  shows "V1' \<in> leaves G (expand_tree G V0)"
  using assms
proof (induction G V0 rule: expand_tree.induct)
  case (1 G V)
  show ?case
  proof (cases "\<T> G V = {||}")
    case True
    then show ?thesis
      using 1(2) 1(3)
      by (simp add: expand_tree.simps)
  next
    case False
    then show ?thesis 
      using expand_tree.simps[of G V]
      using 1(2-) 1(1)
      by (auto split: if_split_asm)
  qed
qed

text \<open>Permutation of a search tree\<close>

primrec perm_tree :: "perm \<Rightarrow> Tree \<Rightarrow> Tree" where
  "perm_tree p (Node V ns) = 
   Node (perm_fun_list p V) ((perm_tree p) |`| ns)"

lemma perm_tree_nodes:
  assumes "V \<in> nodes T"
  shows "perm_fun_list p V \<in> nodes (perm_tree p T)"
  using assms
  by (induction T) auto


text \<open>Lemma 1 - induction\<close>
lemma expand_tree_permute:
  assumes "perm_dom p = num_vertices G" "is_vertex_list G V"
  shows "expand_tree (perm_graph p G) (perm_fun_list p V) =
         perm_tree p (expand_tree G V)"
  using assms
proof (induction G V rule: expand_tree.induct)
  case (1 G V)

  let ?f1 = "\<lambda>v. expand_tree (perm_graph p G) (v # perm_fun_list p V)"
  let ?f1' = "\<lambda>v. expand_tree (perm_graph p G) (perm_fun_list p (v # V))"

  have "(?f1 |`| \<T> (perm_graph p G) (perm_fun_list p V)) = 
        ?f1 |`| perm_fun p |`| \<T> G V"
    using 1(2-3) \<T>_perm
    by (simp add: perm_fun_fset_def)
  also have "... = ?f1' |`| \<T> G V"
    by (auto simp add: perm_fun_list_def)
  also have "... = (\<lambda> v. perm_tree p (expand_tree G (v # V))) |`| (\<T> G V)"
    using 1
    by (metis (no_types, lifting) bot_fset.rep_eq equals0D fset.map_cong0 is_vertex_list_T_extend)
  also have "... = perm_tree p |`| (\<lambda>v. expand_tree G (v # V)) |`| \<T> G V"
    by auto
  finally show ?case
    by (auto simp add: expand_tree.simps[of G V] expand_tree.simps[of "perm_graph p G" "perm_fun_list p V"])
qed

text \<open>Lemma 1\<close>
lemma tree_permute:
  assumes "perm_dom p = num_vertices G"
  shows "tree (perm_graph p G) = perm_tree p (tree G)"
  unfolding tree_def
  using expand_tree_permute[of p G "[]"]
  by (simp add: assms perm_fun_list_def)

lemma leaves_perm_tree:
  assumes "V \<in> leaves G T" "\<forall> V \<in> nodes T. is_vertex_list G V" "perm_dom p = num_vertices G"
  shows "perm_fun_list p V \<in> leaves (perm_graph p G) (perm_tree p T)"
  using assms
proof (induction T)
  case (Node V' ns)
  show ?case
  proof (cases "\<T> G V' = {||}")
    case True
    then have "\<T> (perm_graph p G) (perm_fun_list p V') = {||}"
      using \<T>_perm[of V' G p]
      by (simp add: Node.prems(2) assms(3) perm_fun_fset_def)
    then show ?thesis
      using True
      using Node.prems(1) 
      by auto
  next
    case False
    then have *: "\<T> (perm_graph p G) (perm_fun_list p V') \<noteq> {||}"
      using \<T>_perm[of V' G p]
      by (simp add: Node.prems(2) assms(3) perm_fun_fset_def)
    obtain n where "n \<in> fset ns" "V \<in> leaves G n"
      using False Node.prems(1)
      by auto
    then show ?thesis
      using * False Node(1)[of n] Node.prems      
      by auto
  qed
qed


lemma permute_node_leaves_expand_tree:
  assumes "perm_dom p = num_vertices G" "V \<in> leaves G (expand_tree G V0)" "is_vertex_list G V0"
  shows "perm_fun_list p V \<in> leaves (perm_graph p G) (expand_tree (perm_graph p G) (perm_fun_list p V0))"
  using assms
  by (metis expand_tree_permute leaves_perm_tree target_cell_selector.expand_tree_is_vertex_list target_cell_selector_axioms)

lemma permute_node_leaves:
  assumes "perm_dom p = num_vertices G" "V \<in> leaves G (tree G)"
  shows "perm_fun_list p V \<in> leaves (perm_graph p G) (tree (perm_graph p G))"
  using assms
  by (metis (mono_tags, lifting) One_nat_def \<T>_discrete \<T>_non_discrete fcard_fempty fimage_fempty leD leaves_iff_discrete less_imp_le perm_fun_fset_def perm_tree_nodes \<T>_perm tree_is_vertex_list tree_permute zero_less_Suc)

text \<open>Corollary 2(b)\<close>
lemma expand_tree_permute_automorphism:
  assumes "is_vertex_list G V" "is_automorphism G p" 
  shows "expand_tree G (perm_fun_list p V) = perm_tree p (expand_tree G V)" 
  using assms is_automorphism_def is_isomorphism_def
  by (metis expand_tree_permute)  

text \<open>Special case for the root\<close>
lemma perm_tree_automorphism:
  assumes "is_automorphism G p" 
  shows "perm_tree p (tree G) = tree G"
  using assms
  using tree_permute[of p G]
  unfolding is_automorphism_def is_isomorphism_def
  by auto

text \<open>Corollary 2(a)\<close>
lemma permute_node_automorphism:
  assumes "is_automorphism G p" "V' \<in> nodes (tree G)"
  shows "perm_fun_list p V' \<in> nodes (tree G)"
  using assms
  by (metis perm_tree_automorphism perm_tree_nodes)

lemma permute_node_automorphism_leaves:
  assumes "is_automorphism G p" "V \<in> leaves G (tree G)"
  shows "perm_fun_list p V \<in> leaves G (tree G)"
  using assms
  using permute_node_leaves
  by (metis is_automorphism_def is_isomorphism_def)

lemma permute_node_automorphism_leaves_expand_tree:
  assumes "is_automorphism G p" "V \<in> leaves G (expand_tree G V0)" "is_vertex_list G V0"
  shows "perm_fun_list p V \<in> leaves G (expand_tree G (perm_fun_list p V0))"
  using assms is_automorphism_def is_isomorphism_def permute_node_leaves_expand_tree 
  by fastforce  

lemma pointwise_stabilizer:
  assumes "is_automorphism G p" "is_vertex_list G V" "\<pi> = \<R> G V"         
  shows "is_automorphism (recolor G \<pi>) p \<longleftrightarrow> (\<forall> v \<in> set V. perm_fun p v = v)"
proof
  assume *: "is_automorphism (recolor G \<pi>) p"
  show "\<forall> v \<in> set V. perm_fun p v = v"
  proof
    fix v
    assume "v \<in> set V"

    have "\<forall> v'. vertex G v' \<and> \<pi> v' = \<pi> v \<longrightarrow> v = v'"
    proof-
      have "{v} \<in> set (cells (num_vertices G) \<pi>)"
        using \<open>v \<in> set V\<close> \<R>_cells[of V G v] assms
        by auto
      then obtain c where "{v} = cell (num_vertices G) \<pi> c"
        unfolding cells_def
        by auto
      then show ?thesis
        unfolding cell_def
        by (metis (mono_tags, lifting) empty_Collect_eq insert_not_empty mem_Collect_eq singletonD)
    qed

    moreover

    have **: "vertex G v \<and> vertex G (perm_fun p v)"
      using \<open>is_vertex_list G V\<close> \<open>v \<in> set V\<close>
      by (metis (no_types, lifting) assms(1) atLeastLessThan_iff is_automorphism_def is_isomorphism_def nth_mem perm_dom.rep_eq perm_fun'_def perm_fun.rep_eq perm_list_set subsetD)

    moreover

    have "\<pi> v = \<pi> (perm_fun p v)"
    proof-
      have "(coloring (recolor G \<pi>)) v = 
            (coloring (recolor G \<pi>)) (perm_fun p v)"
        using coloring_permute_node_automorphism[OF *, of v] **
        by (auto simp add: recolor_def)
      then show ?thesis
        using coloring_recolor **
        by auto
    qed

    ultimately 

    show "perm_fun p v = v"
      by auto
  qed
next
  assume "\<forall> v \<in> set V. perm_fun p v = v"
  then have *: "perm_fun_list p V = V"
    by (simp add: map_idI perm_fun_list_def)
  have "colors (perm_graph p (recolor G \<pi>)) = colors (recolor G \<pi>)" 
  proof-
    have "colors (perm_graph p (recolor G \<pi>)) = 
          color_list (num_vertices G) (perm_coloring p (coloring (recolor G \<pi>)))"
      unfolding perm_graph_def recolor_def
      by simp
    also have "... = color_list (num_vertices G) (perm_coloring p \<pi>)"
    proof (rule color_list_eq, safe)
      fix v
      assume "vertex G v"
      then have "vertex G (perm_fun (perm_inv p) v)"
        using assms(1) is_automorphism_def is_isomorphism_def perm_fun_perm_inv_range by blast
      then show "perm_coloring p (coloring (recolor G \<pi>)) v = perm_coloring p \<pi> v"
        by (auto simp add: recolor_def coloring_def color_list_def perm_coloring_def)
    qed
    also have "... = color_list (num_vertices G) \<pi>"
      using assms(1) assms(3) *
      using \<R>_perm[OF assms(2), of p]
      unfolding is_automorphism_def is_isomorphism_def color_list_def
      by (metis color_list_def color_list_eq)
    also have "... = colors (recolor G \<pi>)"
      unfolding recolor_def
      by simp
    finally show ?thesis
      .
  qed
  then show "is_automorphism (recolor G \<pi>) p"
    using assms(1) 
    unfolding is_automorphism_def is_isomorphism_def
    unfolding perm_graph_def recolor_def coloring_def
    by (cases G) auto
qed

definition leaf_perm :: "colored_graph \<Rightarrow> vertex_list \<Rightarrow> perm" where 
  "leaf_perm g V = make_perm (num_vertices g) (\<R> g V)"

end


locale node_invariant = target_cell_selector + 
  fixes \<Phi> :: "colored_graph \<Rightarrow> nat list \<Rightarrow> 'a::linorder"
  assumes \<Phi>_mono: 
    "\<And> G V V'.
       \<lbrakk>is_vertex_list G V; is_vertex_list G V'; \<Phi> G V < \<Phi> G V' \<rbrakk> \<Longrightarrow>
        (\<forall> V1 \<in> leaves G (expand_tree G V). 
         \<forall> V1' \<in> leaves G (expand_tree G V'). \<Phi> G V1 < \<Phi> G V1')"
  assumes \<Phi>_discrete: 
    "\<And> G \<pi> \<pi>' V V'.
       \<lbrakk>is_vertex_list G V; is_vertex_list G V';
        \<pi> = \<R> G V; \<pi>' = \<R> G V';
        is_discrete_coloring (num_vertices G) \<pi>; is_discrete_coloring (num_vertices G) \<pi>' \<rbrakk> \<Longrightarrow>
        \<Phi> G V = \<Phi> G V' \<longleftrightarrow> perm_graph (leaf_perm G V) G = 
                            perm_graph (leaf_perm G V') G"
  assumes \<Phi>_perm:
    "\<And> G V p. 
       \<lbrakk>is_vertex_list G V; perm_dom p = num_vertices G\<rbrakk> \<Longrightarrow>
        \<Phi> (perm_graph p G) (perm_fun_list p V) = \<Phi> G V" 
begin

definition equivalent_leaves where 
  "equivalent_leaves G V V' \<longleftrightarrow> \<Phi> G V = \<Phi> G V'" 


text \<open>Lemma 3 in thesis\<close>
lemma only_automorphism:
  assumes "n_vertex G" "V \<in> leaves G (tree G)" "V' \<in> leaves G (tree G)"
          "perm_fun_list p V = V'"
          "is_automorphism G p"
          "\<pi> = leaf_perm G V"
          "\<pi>' = leaf_perm G V'"
  shows "p = perm_comp (perm_inv \<pi>') \<pi>"
proof-
  let ?n = "num_vertices G"

  have "is_vertex_list G V"
    by (meson assms(2) leaves_iff_discrete tree_is_vertex_list)

  have "perm_dom p = ?n"
    using assms(5) is_automorphism_def is_isomorphism_def by blast

  have "is_perm_fun ?n (\<R> G V)" "is_perm_fun ?n (\<R> G V')"
    using assms(2-3) discrete_coloring_is_permutation target_cell_selector.leaves_iff_discrete target_cell_selector_axioms
    by blast+

  have "perm_comp (perm_inv \<pi>') \<pi> = 
        perm_comp (perm_inv (leaf_perm G V')) \<pi>"
    using assms
    by simp
  also have "... =  perm_comp (perm_inv (make_perm ?n (\<R> G (perm_fun_list p V)))) \<pi>"
    using assms 
    unfolding leaf_perm_def
    by simp
  also have "... = perm_comp (perm_inv (make_perm ?n (\<R> (perm_graph p G) (perm_fun_list p V)))) \<pi>"
    using assms(5) is_automorphism_def is_isomorphism_def by fastforce
  also have "... = perm_comp (perm_inv (make_perm ?n (perm_coloring p (\<R> G V)))) \<pi>"
  proof-
    have "make_perm ?n (\<R> (perm_graph p G) (perm_fun_list p V)) = 
          make_perm ?n (perm_coloring p (\<R> G V))"
    proof (rule make_perm_cong)
      show "\<forall> v. vertex G v \<longrightarrow> \<R> (perm_graph p G) (perm_fun_list p V) v = 
                                perm_coloring p (\<R> G V) v"
        using \<R>_perm \<open>is_vertex_list G V\<close> \<open>is_automorphism G p\<close>
        by (meson is_automorphism_def is_isomorphism_def)
    next
      show "is_perm_fun ?n (\<R> (perm_graph p G) (perm_fun_list p V))"
        using \<open>is_perm_fun (num_vertices G) (\<R> G V')\<close> assms(4) assms(5) is_automorphism_def is_isomorphism_def by auto
    next
      show "is_perm_fun ?n (perm_coloring p (\<R> G V))"
        by (metis \<open>is_perm_fun (num_vertices G) (\<R> G V)\<close> \<open>perm_dom p = num_vertices G\<close> is_perm_fun is_perm_fun_comp perm_dom_perm_inv perm_coloring_def)
    qed
    thus ?thesis
      by simp
  qed
  also have "... = perm_comp (perm_inv (perm_comp \<pi> (perm_inv p))) \<pi>"
    unfolding perm_coloring_def
    by (metis leaf_perm_def \<open>is_perm_fun (num_vertices G) (\<R> G V)\<close> \<open>perm_dom p = ?n\<close> assms(6) is_perm_fun make_perm_perm_fun perm_comp_make_perm perm_dom_perm_inv)
  also have "... = perm_comp (perm_comp p (perm_inv \<pi>)) \<pi>"
    by (simp add: leaf_perm_def \<open>is_perm_fun (num_vertices G) (\<R> G V)\<close> \<open>perm_dom p = ?n\<close> assms(6) perm_inv_inv perm_inv_perm_comp)
  also have "... = p"
    by (simp add: leaf_perm_def \<open>is_perm_fun (num_vertices G) (\<R> G V)\<close> \<open>perm_dom p = ?n\<close> assms(6) perm_comp_assoc perm_comp_perm_inv)
  finally
  show ?thesis
    by simp
qed

lemma equivalent_leaves:
  assumes "n_vertex G" "V \<in> leaves G (tree G)" "V' \<in> leaves G (tree G)"
          "perm_fun_list p V = V'"
          "is_automorphism G p"
  shows "equivalent_leaves G V V'"
proof-
  let ?n = "num_vertices G"

  have "is_vertex_list G V"
    by (meson assms(2) leaves_iff_discrete tree_is_vertex_list)

  have "perm_dom p = ?n"
    using assms(5) is_automorphism_def is_isomorphism_def by blast

  have "\<Phi> G V = \<Phi> (perm_graph p G) (perm_fun_list p V)"
    by (simp add: \<open>is_vertex_list G V\<close> \<open>perm_dom p = num_vertices G\<close> \<Phi>_perm)
  also have "... = \<Phi> G (perm_fun_list p V)"
    using assms(5) is_automorphism_def is_isomorphism_def by auto
  also have "... = \<Phi> G V'"
    using assms
    by simp
  finally
  show ?thesis
    unfolding equivalent_leaves_def
    by simp
qed


theorem 
  assumes "n_vertex G" "V \<in> leaves G (tree G)"
  shows "automorphisms G = { let \<pi> = leaf_perm G V;
                                 \<pi>' = leaf_perm G V'
                              in perm_comp (perm_inv \<pi>') \<pi> | V'. 
                                               V' \<in> leaves G (tree G) \<and>
                                               equivalent_leaves G V V' }"
    (is "?lhs = ?rhs")
proof
  show "?lhs \<subseteq> ?rhs"
  proof
    fix p
    assume "p \<in> automorphisms G"
    let ?V' = "perm_fun_list p V"
    have "?V' \<in> leaves G (tree G)"
      using permute_node_automorphism_leaves[of G p V]
      using \<open>p \<in> automorphisms G\<close> assms automorphisms_def by blast
    have "p = perm_comp (perm_inv (leaf_perm G ?V')) (leaf_perm G V)"
         "equivalent_leaves G V ?V'"
      using only_automorphism[OF assms(1) assms(2) \<open>?V' \<in> leaves G (tree G)\<close>]
      using equivalent_leaves[OF assms(1) assms(2) \<open>?V' \<in> leaves G (tree G)\<close>]
      using \<open>p \<in> automorphisms G\<close> automorphisms_def by blast+
    then show "p \<in> ?rhs"
      using \<open>perm_fun_list p V \<in> leaves G (tree G)\<close> by auto
  qed
next
  show "?rhs \<subseteq> ?lhs"
  proof
    fix p
    let ?n = "num_vertices G"
    assume "p \<in> ?rhs"
    then obtain V' \<pi> \<pi>' where 
      "V' \<in> leaves G (tree G)" "equivalent_leaves G V V'"
      "\<pi> = leaf_perm G V" "\<pi>' = leaf_perm G V'"
      and "p = perm_comp (perm_inv \<pi>') \<pi>"
      by auto
    then have "is_vertex_list G V" "is_vertex_list G V'" 
              "is_discrete_coloring ?n (\<R> G V)"
              "is_discrete_coloring ?n (\<R> G V')"
      using assms(2) leaves_iff_discrete tree_is_vertex_list by blast+

      
    have "is_isomorphism p G G"
      unfolding is_isomorphism_def
    proof
      show "perm_dom p = ?n"
        using \<open>V' \<in> leaves G (tree G)\<close> \<open>\<pi> = leaf_perm G V\<close> \<open>\<pi>' = leaf_perm G V'\<close> \<open>p = perm_comp (perm_inv \<pi>') \<pi>\<close> assms(2) discrete_coloring_is_permutation leaf_perm_def leaves_iff_discrete by force
    next
      show "perm_graph p G = G"
      proof-
        have "perm_graph \<pi> G = perm_graph \<pi>' G"
          using \<Phi>_discrete
          using \<open>equivalent_leaves G V V'\<close> equivalent_leaves_def
          by (simp add: \<open>\<pi> = leaf_perm G V\<close> \<open>\<pi>' = leaf_perm G V'\<close> \<open>is_discrete_coloring (num_vertices G) (\<R> G V')\<close> \<open>is_discrete_coloring (num_vertices G) (\<R> G V)\<close> \<open>is_vertex_list G V'\<close> \<open>is_vertex_list G V\<close>)
        then have "perm_graph (perm_inv \<pi>') (perm_graph \<pi> G) = perm_graph (perm_inv \<pi>') (perm_graph \<pi>' G)"
          by simp
        then have "perm_graph (perm_comp (perm_inv \<pi>') \<pi>) G = perm_graph (perm_comp (perm_inv \<pi>')  \<pi>') G"
          by (simp add: \<open>\<pi> = leaf_perm G V\<close> \<open>\<pi>' = leaf_perm G V'\<close> \<open>is_discrete_coloring (num_vertices G) (\<R> G V')\<close> \<open>is_discrete_coloring (num_vertices G) (\<R> G V)\<close> assms(1) discrete_coloring_is_permutation leaf_perm_def perm_graph_perm_comp)
        then show "perm_graph p G = G"
          by (simp add: \<open>p = perm_comp (perm_inv \<pi>') \<pi>\<close> assms(1) perm_comp_perm_inv perm_graph_permute_id)
      qed
    qed
    then show "p \<in> ?lhs"
      by (simp add: automorphisms_def is_automorphism_def)
  qed
qed

definition max_leaf :: "colored_graph \<Rightarrow> Tree \<Rightarrow> vertex_list" where
  "max_leaf G T = (SOME V. V \<in> leaves G T \<and> (\<forall> V' \<in> leaves G T. \<Phi> G V \<ge> \<Phi> G V'))"

definition canon_form :: "colored_graph \<Rightarrow> colored_graph" where
  "canon_form G = (let V = max_leaf G (tree G) in perm_graph (leaf_perm G V) G)"

lemma canon_formI:
  assumes "V' \<in> leaves G (tree G)" "\<forall> V \<in> leaves G (tree G). \<Phi> G V' \<ge> \<Phi> G V"
  shows "canon_form G = perm_graph (leaf_perm G V') G"
  unfolding canon_form_def Let_def max_leaf_def
proof (rule someI2)
  show "V' \<in> leaves G (tree G) \<and> (\<forall>V\<in>leaves G (tree G). \<Phi> G V \<le> \<Phi> G V')"
    using assms
    by simp
next
  fix V
  assume "V \<in> leaves G (tree G) \<and> (\<forall> V' \<in> leaves G (tree G). \<Phi> G V' \<le> \<Phi> G V)"
  then have "equivalent_leaves G V V'"
    using assms
    unfolding equivalent_leaves_def
    by (simp add: order_class.order.eq_iff)

  then show "perm_graph (leaf_perm G V) G = perm_graph (leaf_perm G V') G"
    using \<open>V \<in> leaves G (tree G) \<and> (\<forall>V'\<in>leaves G (tree G). \<Phi> G V' \<le> \<Phi> G V)\<close>
    using assms
    using \<Phi>_discrete
    using equivalent_leaves_def leaves_iff_discrete tree_is_vertex_list
    by meson
qed         

lemma finite_leaves_expand_tree:
  assumes "is_vertex_list G V"
  shows "finite (leaves G (expand_tree G V))"
  using assms
proof (induction G V rule: expand_tree.induct)
  case (1 G V)
  show ?case
  proof (cases "\<T> G V = {||}")
    case True
    then show ?thesis
      using expand_tree.simps[of G V]
      by simp
  next
    case False
    then show ?thesis
      using expand_tree.simps[of G V]
      using 1 is_vertex_list_T_extend[of V G]
      by auto
  qed
qed

lemma finite_leaves_tree:
  shows "finite (leaves G (tree G))"
  by (simp add: finite_leaves_expand_tree tree_def)

lemma not_empty_leaves_expand_tree:
  assumes "is_vertex_list G V"
  shows "leaves G (expand_tree G V) \<noteq> {}"
  using assms
proof (induction G V rule: expand_tree.induct)
  case (1 G V)
  show ?case
  proof (cases "\<T> G V = {||}")
    case True
    then show ?thesis
      by (simp add: expand_tree.simps)
  next
    case False
    then show ?thesis
      using expand_tree.simps[of G V]
      using 1 local.is_vertex_list_T_extend[of V G]
      by (auto simp add: fmember.rep_eq)
  qed
qed

lemma not_empty_leaves_tree:
  shows "leaves G (tree G) \<noteq> {}"
  by (simp add: not_empty_leaves_expand_tree tree_def)  

lemma ex_max_leaf:
  shows "\<exists> V' \<in> leaves G (tree G). \<forall> V \<in> leaves G (tree G). \<Phi> G V' \<ge> \<Phi> G V"
proof-
  let ?Phi = "{\<Phi> G V' | V'. V' \<in> leaves G (tree G)}"
  let ?M = "Max {\<Phi> G V' | V'. V' \<in> leaves G (tree G)}"
  have *: "finite ?Phi" "?Phi \<noteq> {}"
    by (auto simp add: finite_leaves_tree not_empty_leaves_tree)
  then obtain V' where "\<Phi> G V' = ?M" "V' \<in> leaves G (tree G)"
    using Max_in[of ?Phi]
    by force
  thus ?thesis
    using Max_ge[of ?Phi] *
    by (metis (mono_tags, lifting) mem_Collect_eq)
qed

lemma perm_leaf_perm:
  assumes "perm_dom p = num_vertices G" "V \<in> leaves G (tree G)"
  shows "perm_comp (leaf_perm (perm_graph p G) (perm_fun_list p V)) p =
         leaf_perm G V" (is "?lhs = ?rhs")
proof (rule permEqI)
  have "is_vertex_list G V"
    using assms(2) leaves_iff_discrete tree_is_vertex_list by blast

  have "perm_fun_list p V \<in> leaves (perm_graph p G) (tree (perm_graph p G))"
    by (simp add: assms(1) assms(2) permute_node_leaves)


  show "\<forall> i. vertex G i \<longrightarrow> perm_fun ?lhs i = perm_fun ?rhs i"
  proof safe
    fix v
    assume "vertex G v"

    show "perm_fun ?lhs v = perm_fun ?rhs v"
      using assms \<open>vertex G v\<close> \<open>perm_fun_list p V \<in> leaves (perm_graph p G) (tree (perm_graph p G))\<close> 
      by (smt (verit, ccfv_threshold) \<R>_perm_perm atLeast0LessThan comp_apply discrete_coloring_is_permutation leaf_perm_def leaves_iff_discrete lessThan_iff nth_mem perm_dom.rep_eq perm_dom_make_perm perm_fun'_def perm_fun.rep_eq perm_fun_make_perm perm_fun_perm_comp perm_graph_def perm_list_set select_convs(1) tree_is_vertex_list)      
  qed
next
  show "perm_dom (leaf_perm G V) = num_vertices G"
    using assms(2) discrete_coloring_is_permutation leaf_perm_def leaves_iff_discrete by force
next
  show "perm_dom (perm_comp (leaf_perm (perm_graph p G) (perm_fun_list p V)) p) = num_vertices G "
    using \<open>perm_dom p = num_vertices G\<close> discrete_coloring_is_permutation leaf_perm_def leaves_iff_discrete perm_graph_def 
    by (metis assms(2) perm_dom_make_perm perm_dom_perm_comp select_convs(1) permute_node_leaves)
qed


theorem canon_form:
  shows "is_canon_form canon_form"
  unfolding is_canon_form_def
proof safe
  fix G
  obtain V' where "V' \<in> leaves G (tree G)" "\<forall> V \<in> leaves G (tree G). \<Phi> G V' \<ge> \<Phi> G V"
    using ex_max_leaf
    by blast
  then show "isomorphic G (canon_form G)"
    unfolding isomorphic_def is_isomorphism_def
    by (rule_tac x="leaf_perm G V'" in exI)
       (simp add: canon_formI discrete_coloring_is_permutation leaf_perm_def leaves_iff_discrete)
next
  fix G :: colored_graph and p
  assume "perm_dom p = num_vertices G" "n_vertex G"
  obtain V' where V': "V' \<in> leaves G (tree G)" "\<forall> V \<in> leaves G (tree G). \<Phi> G V' \<ge> \<Phi> G V"
    using ex_max_leaf
    by blast
  let ?pG = "perm_graph p G"
  let ?pV' = "perm_fun_list p V'"
  have "?pV' \<in> leaves (perm_graph p G) (perm_tree p (tree G))"
    using V'(1) \<open>perm_dom p = num_vertices G\<close> permute_node_leaves tree_permute by force
  then have pV'1: "?pV' \<in> leaves ?pG (tree ?pG)"
    by (simp add: \<open>perm_dom p = num_vertices G\<close> tree_permute)

  have "\<Phi> ?pG ?pV' = \<Phi> G V'"
    by (meson \<Phi>_perm \<open>V' \<in> leaves G (tree G)\<close> \<open>perm_dom p = num_vertices G\<close> leaves_iff_discrete tree_is_vertex_list)

  have pV'2: "\<forall> V \<in> leaves ?pG (tree ?pG). \<Phi> ?pG ?pV' \<ge> \<Phi> ?pG V"
  proof safe
    fix V
    assume "V \<in> leaves ?pG (tree ?pG)"
    then have "perm_fun_list (perm_inv p) V \<in> leaves G (tree G)"
      using \<open>n_vertex G\<close> \<open>perm_dom p = num_vertices G\<close> 
      using permute_node_leaves[of "perm_inv p" ?pG V]
      by (simp add: perm_comp_perm_inv perm_graph_perm_comp perm_graph_permute_id)
    then have "\<Phi> G (perm_fun_list (perm_inv p) V) \<le> \<Phi> G V'"
      using V'(2)[rule_format]
      by simp
    moreover
    have "\<Phi> G (perm_fun_list (perm_inv p) V) = \<Phi> (perm_graph p G) V"
      using \<open>V \<in> leaves ?pG (tree ?pG)\<close> \<open>n_vertex G\<close> \<open>perm_dom p = num_vertices G\<close> 
      by (smt (verit, ccfv_SIG) leaves_iff_discrete node_invariant.\<Phi>_perm node_invariant_axioms perm_comp_perm_inv perm_dom_perm_inv perm_graph_def perm_graph_perm_comp perm_graph_permute_id simps(1) tree_is_vertex_list)
    ultimately 
    have "\<Phi> (perm_graph p G) V \<le> \<Phi> G V'"
      by auto
    thus "\<Phi> ?pG ?pV' \<ge> \<Phi> ?pG V"
      by (simp add: \<open>\<Phi> (perm_graph p G) (perm_fun_list p V') = \<Phi> G V'\<close>)
  qed

  have "canon_form ?pG = perm_graph (leaf_perm ?pG ?pV') ?pG"
    using canon_formI[OF pV'1 pV'2]
    by simp
  also have "... = perm_graph (perm_comp (leaf_perm ?pG ?pV') p) G"
    using \<open>n_vertex G\<close> \<open>perm_dom p = num_vertices G\<close> discrete_coloring_is_permutation leaf_perm_def leaves_iff_discrete pV'1 perm_graph_def perm_graph_perm_comp by auto
  also have "... = perm_graph (leaf_perm G V') G"
    using V'(1) \<open>perm_dom p = num_vertices G\<close> perm_leaf_perm by presburger
  also have "... = canon_form G"
    using canon_formI[OF V'(1-2)]
    by simp
  finally show "canon_form (perm_graph p G) = canon_form G"
    .
qed

primrec node_vertex_list where
  "node_vertex_list (Node V ns) = V"

primrec prune_node :: "Tree \<Rightarrow> Tree \<Rightarrow> Tree" where                   
  "prune_node (Node V ns) n = 
   (Node V ((ffilter (\<lambda> n'. n' \<noteq> n) ((\<lambda> n'. prune_node n' n) |`| ns))))"

definition prune_nodes :: "Tree \<Rightarrow> Tree list \<Rightarrow> Tree" where
  "prune_nodes T Vs = foldl prune_node T Vs"

lemma prune_nodes_Nil [simp]:
  shows "prune_nodes T [] = T"
  by (simp add: prune_nodes_def)

lemma prune_nodes_snoc [simp]:
  shows "prune_nodes T (Vs @ [V]) = prune_node (prune_nodes T Vs) V"
  by (simp add: prune_nodes_def)

definition pruneA :: "colored_graph \<Rightarrow> vertex_list \<Rightarrow> vertex_list \<Rightarrow> bool" where
  "pruneA G V1 V2 \<longleftrightarrow> 
      V1 \<in> nodes (tree G) \<and> V2 \<in> nodes (tree G) \<and> length V1 = length V2 \<and>
       \<Phi> G V1 > \<Phi> G V2"

definition pruneB :: "colored_graph \<Rightarrow> vertex_list \<Rightarrow> vertex_list \<Rightarrow> bool" where
  "pruneB G V1 V2 \<longleftrightarrow> 
      V1 \<in> nodes (tree G) \<and> V2 \<in> nodes (tree G) \<and> length V1 = length V2 \<and>
       \<Phi> G V1 \<noteq> \<Phi> G V2"

definition pruneC :: "colored_graph \<Rightarrow> vertex_list \<Rightarrow> vertex_list \<Rightarrow> bool" where
  "pruneC G V1 V2 \<longleftrightarrow>
      V1 \<in> nodes (tree G) \<and> V2 \<in> nodes (tree G) \<and> rev V1 < rev V2 \<and>
     (\<exists> p \<in> automorphisms G. perm_fun_list p V1 = V2)"
     

definition pruneAs :: "colored_graph \<Rightarrow> vertex_list list \<Rightarrow> bool" where
  "pruneAs G Vs \<longleftrightarrow> (\<forall> V2 \<in> set Vs. \<exists> V1. pruneA G V1 V2)"

definition pruneACs :: "colored_graph \<Rightarrow> vertex_list list \<Rightarrow> bool" where
  "pruneACs G Vs \<longleftrightarrow> (\<forall> V2 \<in> set Vs. \<exists> V1. pruneA G V1 V2 \<or> pruneC G V1 V2)"

lemma nodes_prune_node:
  shows "nodes (prune_node T V) \<subseteq> nodes T"
  by (induction T) auto

lemma leaves_prune_node:
  shows "leaves G (prune_node T V) \<subseteq> leaves G T"
  by (induction T) auto  
                                                  
lemma leaves_prune_nodes:
  shows "leaves G (prune_nodes T Vs) \<subseteq> leaves G T"
proof (induction Vs rule: rev_induct)
  case Nil
  then show ?case
    by simp
next 
  case (snoc V Vs)
  thus ?case
    using leaves_prune_node
    by force
qed


lemma leaves_prune_nodeI:
  assumes "V \<notin> leaves G T'" "V \<in> leaves G T"
  shows "V \<in> leaves G (prune_node T T')"
  using assms
proof (induction T)
  case (Node V' ns')
  show ?case
  proof (cases "\<T> G V' = {||}")
    case True
    then show ?thesis
      using Node.prems
      by simp
  next
    case False
    then show ?thesis
      using Node
      by force
  qed
qed


lemma pruneAs_remain_max:
  assumes "pruneAs G Vs" "Max\<Phi> = Max {\<Phi> G V | V. V \<in> leaves G (tree G)}" 
  shows "\<forall> V \<in> leaves G (tree G). \<Phi> G V = Max\<Phi> \<longrightarrow> 
           V \<in> leaves G (prune_nodes (tree G) (map (expand_tree G) Vs))"
  using assms
proof (induction Vs rule: rev_induct)
  case Nil
  show ?case
    by simp
next
  case (snoc V2 Vs)

  let ?Phi = "{\<Phi> G V |V. V \<in> leaves G (tree G)}"
  have "finite ?Phi \<and> ?Phi \<noteq> {}"
    using not_empty_leaves_tree[of G] finite_leaves_tree[of G]
    by auto

  show ?case
  proof safe
    fix V
    assume "V \<in> leaves G (tree G)" "Max\<Phi> = \<Phi> G V" 
    then obtain V1 where
      1: "V \<in> leaves G (prune_nodes (tree G) (map (expand_tree G) Vs))"
         "pruneA G V1 V2"
      using snoc
      unfolding pruneAs_def pruneA_def
      by auto

    have 2: "\<Phi> G V1 > \<Phi> G V2" 
            "length V1 = length V2" "V1 \<in> nodes (tree G)" "V2 \<in> nodes (tree G)"
      using \<open>pruneA G V1 V2\<close>
      unfolding pruneA_def
      by auto

    obtain V1' where "V1' \<in> leaves G (expand_tree G V1)"
      by (meson \<open>V1 \<in> nodes (tree G)\<close> ex_in_conv not_empty_leaves_expand_tree tree_is_vertex_list)

    have "V \<notin> leaves G (expand_tree G V2)"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      then have "\<Phi> G V1' > \<Phi> G V"
        using \<Phi>_mono[of V2 G V1, rule_format, of V V1']
        using \<open>V1 \<in> nodes (tree G)\<close> \<open>V1' \<in> leaves G (expand_tree G V1)\<close> \<open>V2 \<in> nodes (tree G)\<close> \<open>\<Phi> G V2 < \<Phi> G V1\<close> tree_is_vertex_list by presburger
      then have "\<Phi> G V1' > Max ?Phi"
        using snoc(3) \<open>Max\<Phi> = \<Phi> G V\<close>
        by simp
      moreover
      have "\<Phi> G V1' \<in> ?Phi"
        using \<open>V1' \<in> leaves G (expand_tree G V1)\<close> \<open>V1 \<in> nodes (tree G)\<close>
        using leaves_of_node tree_def
        by auto
      ultimately
      show False
        using \<open>finite ?Phi \<and> ?Phi \<noteq> {}\<close>
        by (meson Max_ge  leD)
    qed

    then have "V \<in> leaves G (prune_node (prune_nodes (tree G) (map (expand_tree G) Vs)) (expand_tree G V2))"
      using 1
      by (simp add: leaves_prune_nodeI)

    then show "V \<in> leaves G (prune_nodes (tree G) (map (expand_tree G) (Vs @ [V2])))"
      using 1
      by auto
  qed
qed

lemma perm_fun_list_perm_inv:
  assumes "perm_dom p = n" "set xs \<subseteq> {0..<n}"
  shows "perm_fun_list (perm_inv p) (perm_fun_list p xs) = xs"
  using assms
  by (metis atLeast0LessThan lessThan_iff map_idI map_map perm_fun_list_def perm_fun_perm_inv2 subset_eq)

lemma is_automorphism_perm_inv:
  assumes "is_automorphism G p" "n_vertex G"
  shows "is_automorphism G (perm_inv p)"
  unfolding is_automorphism_def is_isomorphism_def
  using assms
  by (smt (verit) is_automorphism_def is_isomorphism_def perm_comp_perm_id_1 perm_comp_perm_inv perm_dom_perm_comp perm_dom_perm_inv perm_graph_perm_comp)

lemma lexord_right_append:
  assumes "(xs, ys) \<in> lexord R" "length xs = length ys"
  shows "(xs @ xs', ys @ ys') \<in> lexord R"
  using assms
  unfolding lexord_def
  by auto blast+

lemma list_less_right_append:
  assumes "length xs = length ys" "xs < ys"
  shows "xs @ xs' < ys @ ys'"
  using assms
  by (simp add: list_less_def lexord_right_append)

lemma leaves_suffix:
  assumes "V' \<in> leaves G (expand_tree G V)"
  shows "\<exists> k. drop k V' = V"
  using assms
proof (induction G V rule: expand_tree.induct)
  case (1 G V)
  show ?case
  proof (cases "\<T> G V = {||}")
    case True
    then show ?thesis
      using 1(2) expand_tree.simps[of G V]
      by (metis drop0 leaves.simps singleton_iff)
  next
    case False
    then obtain n where "n \<in> fset (\<T> G V)" "V' \<in> leaves G (expand_tree G (n # V))"
      using 1(2) expand_tree.simps[of G V]
      by auto
    then obtain k where "drop k V' = n # V"
      using 1(1) False
      by auto
    then show ?thesis
      by (metis Cons_nth_drop_Suc drop_all_iff list.distinct(1) list.inject not_le)
  qed
qed

lemma pruneACs_remain_max:
  assumes "pruneACs G Vs" "n_vertex G"
          "Phi = {\<Phi> G V | V. V \<in> leaves G (tree G)}"
          "MaxPhi = {rev V | V. V \<in> leaves G (tree G) \<and> \<Phi> G V = Max Phi}"
  shows "rev (Min MaxPhi) \<in> leaves G (prune_nodes (tree G) (map (expand_tree G) Vs))"
proof-
  let ?V = "Min MaxPhi"
  have "finite Phi \<and> Phi \<noteq> {}"
    using not_empty_leaves_tree[of G] finite_leaves_tree[of G]
    using \<open>Phi = {\<Phi> G V | V. V \<in> leaves G (tree G)}\<close>
    by auto
  then have "finite {V. V \<in> leaves G (tree G) \<and> \<Phi> G V = Max Phi} \<and> 
             {V. V \<in> leaves G (tree G) \<and> \<Phi> G V = Max Phi} \<noteq> {}"
    using finite_leaves_tree[of G]
    using \<open>Phi = {\<Phi> G V | V. V \<in> leaves G (tree G)}\<close>
    by (smt (verit, best) Max_in empty_Collect_eq mem_Collect_eq rev_finite_subset subsetI)
  then have "finite MaxPhi \<and> MaxPhi \<noteq> {}"
    using \<open>MaxPhi = {rev V |V. V \<in> leaves G (tree G) \<and> \<Phi> G V = Max Phi}\<close>
    by auto
  then have Min: "rev ?V \<in> leaves G (tree G)" "\<Phi> G (rev ?V) = Max Phi" 
    "\<forall> V' \<in> leaves G (tree G). \<Phi> G V' = Max Phi \<longrightarrow> rev V' \<ge> ?V"
    using assms(4) Min_eq_iff eq_Min_iff Min_le
    using \<open>finite MaxPhi \<and> MaxPhi \<noteq> {}\<close>
    using \<open>MaxPhi = {rev V |V. V \<in> leaves G (tree G) \<and> \<Phi> G V = Max Phi}\<close>
    by fastforce+
  show ?thesis
    using \<open>pruneACs G Vs\<close>
  proof (induction Vs rule: rev_induct)
    case Nil                                  
    then show ?case
      using Min
      by simp
  next
    case (snoc V2 Vs)
    obtain V1 where 
      1: "rev ?V \<in> leaves G (prune_nodes (tree G) (map (expand_tree G) Vs))"
      "pruneA G V1 V2 \<or> pruneC G V1 V2"
      using snoc
      unfolding pruneACs_def
      by auto

    show ?case
      using \<open>pruneA G V1 V2 \<or> pruneC G V1 V2\<close>
    proof
      assume "pruneA G V1 V2"
      then have 2: "\<Phi> G V1 > \<Phi> G V2" 
                   "length V1 = length V2" 
                   "V1 \<in> nodes (tree G)" "V2 \<in> nodes (tree G)"
        using \<open>pruneA G V1 V2\<close>
        unfolding pruneA_def
        by auto

      have "rev ?V \<notin> leaves G (expand_tree G V2)"
      proof (rule ccontr)
        assume "\<not> ?thesis"

        obtain V1' where "V1' \<in> leaves G (expand_tree G V1)"
          by (meson \<open>V1 \<in> nodes (tree G)\<close> ex_in_conv not_empty_leaves_expand_tree tree_is_vertex_list)

        have "\<Phi> G V1' > \<Phi> G (rev ?V)"
          using \<open>\<not> rev ?V \<notin> leaves G (expand_tree G V2)\<close>
          using \<Phi>_mono[of V2 G V1, rule_format, of "rev ?V" V1']
          using \<open>V1 \<in> nodes (tree G)\<close> \<open>V1' \<in> leaves G (expand_tree G V1)\<close> \<open>V2 \<in> nodes (tree G)\<close> \<open>\<Phi> G V2 < \<Phi> G V1\<close> tree_is_vertex_list
          by presburger
        then have "\<Phi> G V1' > Max Phi"
          using \<open>\<Phi> G (rev ?V) = Max Phi\<close>
          by simp
        moreover
        have "\<Phi> G V1' \<in> Phi"
          using \<open>V1' \<in> leaves G (expand_tree G V1)\<close> \<open>V1 \<in> nodes (tree G)\<close>
          using \<open>Phi = {\<Phi> G V | V. V \<in> leaves G (tree G)}\<close>
          using leaves_of_node tree_def
          by auto
        ultimately
        show False
          using \<open>finite Phi \<and> Phi \<noteq> {}\<close>
          by (meson Max_ge  leD)
      qed

      then have "rev ?V \<in> leaves G (prune_node (prune_nodes (tree G) (map (expand_tree G) Vs)) (expand_tree G V2))"
        using 1
        by (simp add: leaves_prune_nodeI)

      then show ?case
        using 1
        by auto
    next
      assume "pruneC G V1 V2"
      then obtain p where 
        2: "p \<in> automorphisms G" "perm_fun_list p V1 = V2" 
           "rev V1 < rev V2" "V1 \<in> nodes (tree G)" "V2 \<in> nodes (tree G)"
        unfolding pruneC_def
        by auto

      then have "length V1 = length V2"
        unfolding perm_fun_list_def
        by auto

      have "is_vertex_list G V1" "is_vertex_list G V2"
        using 2 tree_is_vertex_list 
        by blast+
      then have "perm_fun_list (perm_inv p) V2 = V1"
        using 2
        unfolding automorphisms_def is_automorphism_def is_isomorphism_def
        using perm_fun_list_perm_inv by fastforce

      have "is_vertex_list G (rev ?V)"
        using Min(1) leaves_iff_discrete target_cell_selector.tree_is_vertex_list target_cell_selector_axioms
        by blast

      have "rev ?V \<notin> leaves G (expand_tree G V2)"
      proof (rule ccontr)
        assume "\<not> ?thesis"
        let ?pV1 = "perm_fun_list p V1"
        let ?pV = "perm_fun_list (perm_inv p) (rev ?V)"

        have "expand_tree G ?pV1 = perm_tree p (expand_tree G V1)"
          using 2
          using expand_tree_permute_automorphism[of V1 G p]
          using \<open>is_vertex_list G V1\<close> automorphisms_def
          by blast

        have "?pV \<in> leaves G (expand_tree G V1)"
        proof-
          have "is_automorphism G (perm_inv p)"
            using "2"(1) assms(2) automorphisms_def is_automorphism_perm_inv
            by blast
          then show ?thesis
            using \<open>\<not> rev ?V \<notin> leaves G (expand_tree G V2)\<close> \<open>is_vertex_list G V2\<close> 
              \<open>perm_fun_list (perm_inv p) V2 = V1\<close>
              permute_node_automorphism_leaves_expand_tree 
            by blast
        qed

        then have "?pV \<in> leaves G (tree G)"
          by (metis "2"(4) leaves_of_node tree_def)
        moreover
        have "\<Phi> G ?pV = Max Phi"
          using \<open>Phi = {\<Phi> G V | V. V \<in> leaves G (tree G)}\<close>
          using  \<open>MaxPhi = {rev V | V. V \<in> leaves G (tree G) \<and> \<Phi> G V = Max Phi}\<close>
          using \<open>is_vertex_list G (rev ?V)\<close>
          using \<Phi>_perm[where p="perm_inv p" and G = G and V = "rev ?V"]
          using \<open>p \<in> automorphisms G\<close>
          unfolding automorphisms_def is_automorphism_def is_isomorphism_def
          by (metis (no_types, lifting) "2"(1) Min(1) Min(2) assms(2) automorphisms_def calculation equivalent_leaves is_automorphism_perm_inv mem_Collect_eq node_invariant.equivalent_leaves_def node_invariant_axioms)
        ultimately
        have "rev ?pV \<in> MaxPhi"
          using  \<open>MaxPhi = {rev V | V. V \<in> leaves G (tree G) \<and> \<Phi> G V = Max Phi}\<close>
          by simp

        then have "rev ?pV \<ge> ?V"
          by (simp add: \<open>finite MaxPhi \<and> MaxPhi \<noteq> {}\<close>)

        moreover

        have "\<exists> k. drop k ?pV = V1"
          using `?pV \<in> leaves G (expand_tree G V1)`
          using leaves_suffix by blast

        moreover

        have "\<exists> k. drop k (rev ?V) = V2"
          using `\<not> rev ?V \<notin> leaves G (expand_tree G V2)`
          using leaves_suffix by blast
          

        ultimately

        show False
          using \<open>rev V1 < rev V2\<close> \<open>length V1 = length V2\<close>
          using list_less_right_append[of V1 V2]
          by (metis append_take_drop_id leD length_rev list_less_right_append rev_append rev_rev_ident)
      qed

      then have "rev ?V \<in> leaves G (prune_node (prune_nodes (tree G) (map (expand_tree G) Vs)) (expand_tree G V2))"
        using 1
        by (simp add: leaves_prune_nodeI)

      then show ?case
        using 1
        by auto
    qed
  qed
qed

lemma pruneACs_canon_form:
  assumes "n_vertex G" "pruneACs G Vs"
          "T = prune_nodes (tree G) (map (expand_tree G) Vs)"
  shows "canon_form G = perm_graph (leaf_perm G (max_leaf G T)) G"
proof-
  let ?Phi = "{\<Phi> G V | V. V \<in> leaves G (tree G)}"
  let ?MaxPhi = "{rev V | V. V \<in> leaves G (tree G) \<and> \<Phi> G V = Max ?Phi}"
  let ?v = "Min ?MaxPhi"
  
  have "finite ?Phi" "?Phi \<noteq> {}"
    using not_empty_leaves_tree[of G] finite_leaves_tree[of G]
    by auto
  then have "finite {V. V \<in> leaves G (tree G) \<and> \<Phi> G V = Max ?Phi}" 
             "{V. V \<in> leaves G (tree G) \<and> \<Phi> G V = Max ?Phi} \<noteq> {}"
    using finite_leaves_tree[of G]
    by (smt (verit, best) Max_in empty_Collect_eq mem_Collect_eq rev_finite_subset subsetI)+
  then have "finite ?MaxPhi" "?MaxPhi \<noteq> {}"
    by auto

  have "\<forall> V \<in> leaves G (tree G). \<Phi> G V \<le> Max ?Phi"
    using Max_ge \<open>finite ?Phi\<close> \<open>?Phi \<noteq> {}\<close>
    by blast

  have "?v \<in> ?MaxPhi"
    using Min_in \<open>finite ?MaxPhi\<close> \<open>?MaxPhi \<noteq> {}\<close> 
    by blast
  then have "\<Phi> G (rev ?v) = Max ?Phi"
    by fastforce

  have *: "rev ?v \<in> leaves G T"
          "\<forall>V'\<in>leaves G T. \<Phi> G V' \<le> \<Phi> G (rev ?v)"
    using pruneACs_remain_max[OF assms(2) assms(1), of ?Phi ?MaxPhi] assms(3)
    using \<open>finite ?MaxPhi\<close> \<open>?MaxPhi \<noteq> {}\<close> \<open>finite ?Phi\<close> \<open>?Phi \<noteq> {}\<close> 
    by (smt (verit) Max_ge Min_in leaves_prune_nodes mem_Collect_eq rev_rev_ident subset_iff)+

  then have **: "max_leaf G T \<in> leaves G T" 
                "\<forall>V'\<in>leaves G T. \<Phi> G V' \<le> \<Phi> G (max_leaf G T)"
    unfolding max_leaf_def
    by (smt (verit, best) some_eq_imp)+

  have "max_leaf G T \<in> leaves G (tree G)"
    using **
    using assms(3) leaves_prune_nodes
    by blast
    
  show ?thesis
  proof (rule canon_formI)
    show "max_leaf G T \<in> leaves G (tree G)"
      by fact
  next
    show "\<forall> V \<in> leaves G (tree G). \<Phi> G V \<le> \<Phi> G (max_leaf G T)"
    proof
      fix V
      assume "V \<in> leaves G (tree G)"
      have "max_leaf G T \<in> {V \<in> leaves G (tree G). \<Phi> G V = Max ?Phi}"
      proof safe
        show "max_leaf G T \<in> leaves G (tree G)"
          by fact
      next
        show "\<Phi> G (max_leaf G T) = Max ?Phi"
        proof (rule Max_eqI[symmetric])
          show "finite ?Phi"
            using \<open>finite ?Phi\<close> \<open>?Phi \<noteq> {}\<close>
            by blast
        next
          show "\<Phi> G (max_leaf G T) \<in> ?Phi"
            using \<open>max_leaf G T \<in> leaves G (tree G)\<close> by blast
        next
          fix phi
          assume "phi \<in> ?Phi"
          then have "phi \<le> Max ?Phi"
            by (simp add: \<open>finite ?Phi\<close> \<open>?Phi \<noteq> {}\<close>)
          then have "phi \<le> \<Phi> G (rev ?v)"
            by (simp add: \<open>\<Phi> G (rev ?v) = Max ?Phi\<close>)
          then show "phi \<le> \<Phi> G (max_leaf G T)"
            using *(1) **(2)
            by auto
        qed
      qed
      then show "\<Phi> G V \<le> \<Phi> G (max_leaf G T)"
        using \<open>V \<in> leaves G (tree G)\<close>
        using \<open>\<forall>V\<in>leaves G (tree G). \<Phi> G V \<le> Max ?Phi\<close>
        by simp
    qed
  qed
qed

end

end