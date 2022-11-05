theory ProofFormat
  imports Main GraphIsomorphism
begin 

type_synonym color_list = "nat list"
type_synonym node = "nat list"
type_synonym vertex = nat

datatype rule = 
     ColoringAxiom
   | Individualize node vertex color_list

datatype fact = 
      ColoringEqual node color_list
   |  ColoringFiner node color_list
   |  Canonical node color_list 

record fact_database = 
  graph :: colored_graph
  facts :: "fact set"

definition add_fact :: "fact_database \<Rightarrow> fact \<Rightarrow> fact_database" where
  "add_fact fd f = fd \<lparr> facts := (facts fd) \<union> {f}  \<rparr>"

definition individualize :: "color_list \<Rightarrow> vertex \<Rightarrow> color_list" where 
  "individualize cl v = (
      let n = length cl 
       in Coloring.color_list n (GraphIsomorphism.individualize (Coloring.coloring n cl) v))"

primrec check_rule :: "rule \<Rightarrow> fact_database \<Rightarrow> fact_database option" where
  "check_rule ColoringAxiom fd = Some (add_fact fd (ColoringFiner [] (colors (graph fd))))"
| "check_rule (Individualize \<nu> v \<pi>) fd = (
      if ColoringEqual \<nu> \<pi> \<notin> facts fd then None
      else Some (add_fact fd (ColoringFiner (v # \<nu>) (individualize \<pi> v)))
  )"

type_synonym graph_proof = "rule list"
definition run_proof :: "colored_graph \<Rightarrow> graph_proof \<Rightarrow> fact_database option" where
  "run_proof g pf = (
     let initial_fd = Some \<lparr> graph = g, facts = {} \<rparr> 
      in fold (\<lambda> r fdo. case fdo of None \<Rightarrow> None | Some fd \<Rightarrow> check_rule r fd) pf initial_fd)" 

theorem
  assumes "Some fd = run_proof g pf"
  assumes "Canonical \<nu> \<pi> \<in> facts fd"
  shows "True" (* graf dobijen permutacijom \<pi> je kanonska forma grafa g *)

end