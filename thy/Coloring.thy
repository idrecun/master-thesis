theory Coloring
  imports Main Permutation
begin

text \<open>Graph coloring as a function (only for convenience)\<close>
type_synonym coloring = "nat \<Rightarrow> nat"

text \<open>We assume that only relevant nodes are 0 to n-1 so this gives the colooring 
representation in a form of a list\<close>
definition color_list :: "nat \<Rightarrow> coloring \<Rightarrow> nat list" where
  "color_list n \<pi> = map \<pi> [0..<n]"

lemma color_list_eq:
  assumes "\<forall> x < n. f1 x = f2 x"
  shows "color_list n f1 = color_list n f2"
  using assms
  unfolding color_list_def
  by auto

text \<open>All colors used in a coloring\<close>
definition all_colors :: "nat \<Rightarrow> coloring \<Rightarrow> nat set" where
  "all_colors n \<pi> = \<pi> ` {0..<n}"

text \<open>Number of colors used\<close>
definition num_colors :: "nat \<Rightarrow> coloring \<Rightarrow> nat" where
  "num_colors n \<pi> = card (all_colors n \<pi>)"

text \<open>Cell of a coloring is the set of all vertices colored by the given color\<close>
definition cell :: "nat \<Rightarrow> coloring \<Rightarrow> nat \<Rightarrow> nat set" where
  "cell n \<pi> c = {v. v < n \<and> \<pi> v = c}"

text \<open>The list of all cells of a given coloring (some might be empty)\<close>
definition cells :: "nat \<Rightarrow> coloring \<Rightarrow> (nat set) list" where
  "cells n \<pi> = map (\<lambda> c. cell n \<pi> c) [0..<num_colors n \<pi>]" 


lemma cells_disjunct:
  assumes "a \<in> c1" "a \<in> c2" "c1 \<in> set (cells n \<pi>)" "c2 \<in> set (cells n \<pi>)"
  shows "c1 = c2"
  using assms
  unfolding cells_def
  by (auto simp add: cell_def)

text \<open>Nodes 0 to n-1 are colored using all colors from 0 to k-1 for some k\<close>
definition consecutive :: "nat \<Rightarrow> coloring \<Rightarrow> bool" where
  "consecutive n \<pi> \<longleftrightarrow> all_colors n \<pi> = {0..<num_colors n \<pi>}"

text \<open>Check if the color \<pi>' refines the coloring \<pi> - each cells of \<pi>' is a subset of a cell of \<pi>\<close>
definition finer :: "nat \<Rightarrow> coloring \<Rightarrow> coloring \<Rightarrow> bool" (infixl "\<preceq>" 100) where
  "finer n \<pi>' \<pi> \<longleftrightarrow> (\<forall> v < n. \<forall> w < n. \<pi> v < \<pi> w \<longrightarrow> \<pi>' v < \<pi>' w)"

lemma finer_same_color:
  assumes "finer n \<pi>' \<pi>" "v1 < n" "v2 < n" "\<pi>' v1 = \<pi>' v2" 
  shows "\<pi> v1 = \<pi> v2"
  using assms
  unfolding finer_def
  by (metis less_imp_not_eq less_linear)

lemma finer_cell_subset:
  assumes "n > 0" "finer n \<pi>' \<pi>" "consecutive n \<pi>"
  shows "\<forall> c' \<in> set (cells n \<pi>'). \<exists> c \<in> set (cells n \<pi>). c' \<subseteq> c"
proof safe
  fix c'
  assume "c' \<in> set (cells n \<pi>')"
  show "\<exists> c \<in> set (cells n \<pi>). c' \<subseteq> c"
  proof (cases "c' = {}")
    case True
    then show ?thesis
      using \<open>n > 0\<close>
      by (auto simp add: cells_def num_colors_def all_colors_def)
  next
    case False
    then obtain v where "v < n" "v \<in> c'"
      using \<open>c' \<in> set (cells n \<pi>')\<close>
      unfolding cell_def cells_def
      by auto
    let ?c = "cell n \<pi> (\<pi> v)"
    have "?c \<in> set (cells n \<pi>)"
      using \<open>v < n\<close> \<open>consecutive n \<pi>\<close>
      unfolding cells_def consecutive_def
      by (auto simp add: num_colors_def all_colors_def)
    moreover
    have "c' \<subseteq> ?c"
    proof
      fix v'
      assume "v' \<in> c'"
      then have "v' < n" "\<pi>' v' = \<pi>' v"
        using \<open>c' \<in> set (cells n \<pi>')\<close> \<open>v \<in> c'\<close>
        unfolding cells_def cell_def
        by auto
      then have "\<pi> v' = \<pi> v"
        using \<open>v < n\<close> \<open>finer n \<pi>' \<pi>\<close> finer_same_color 
        by blast
      then show "v' \<in> ?c"
        using \<open>v' < n\<close>
        unfolding cell_def
        by auto
    qed
    ultimately
    show ?thesis
      by auto
  qed
qed

text \<open>A coloring is discrete if each vertex is colored by a different color {0..<n}\<close>
definition is_discrete_coloring :: "nat \<Rightarrow> coloring \<Rightarrow> bool" where
  "is_discrete_coloring n \<pi> \<longleftrightarrow> all_colors n \<pi> = {0..<n}"

lemma discrete_coloring_is_permutation:
  assumes "is_discrete_coloring n \<pi>"
  shows "is_perm_fun n \<pi>"
  using assms finite_surj_inj[of "{0..<n}" \<pi>]
  unfolding is_discrete_coloring_def is_perm_fun_def all_colors_def
  unfolding bij_betw_def 
  by auto

end