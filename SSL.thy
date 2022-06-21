theory SSL
imports "HOL-Library.Finite_Map"
begin

section \<open>Syntax and semantics\<close>

subsubsection \<open>Basic types and syntax.\<close>
text \<open>Linear ordered variables with an explicit nil element.\<close>
datatype var = Nil | Var nat

instantiation var :: linorder begin
fun less_eq_var :: "var \<Rightarrow> var \<Rightarrow> bool" where
  "less_eq_var Nil _ = True"
| "less_eq_var _ Nil = False"
| "less_eq_var (Var v1) (Var v2) = (v1 \<le> v2)"

fun less_var :: "var \<Rightarrow> var \<Rightarrow> bool" where
  "less_var Nil Nil = False"
| "less_var Nil _ = True"
| "less_var _ Nil = False"
| "less_var (Var v1) (Var v2) = (v1 < v2)"
instance apply standard apply (auto simp: elim!: less_eq_var.elims less_var.elims)
  by (metis less_eq_var.elims(3) nle_le var.inject var.simps(3))
end

text \<open>SSL formulae.\<close>
datatype form = 
  Emp 
| PointsTo var var  (infix "\<mapsto>\<^sub>s" 70)
| LS "var\<times>var"      ("ls_")
| Eq var var        (infix "=\<^sub>s" 70)
| NEq var var       (infix "\<noteq>\<^sub>s" 70)
| SepConj form form (infixl "\<^emph>" 80)
| Septraction form form (infix "-\<otimes>" 60)
| Conj form form    (infixl "\<and>\<^sub>s" 65)
| Disj form form    (infixl "\<or>\<^sub>s" 60)
| Neg form          ("\<not>\<^sub>s _")

abbreviation t :: form where "t \<equiv> Emp \<or>\<^sub>s \<not>\<^sub>sEmp"

fun size :: "form \<Rightarrow> nat" where
  "size Emp = 1"
| "size (PointsTo _ _) = 1"
| "size (LS _) = 1"
| "size (Eq _ _) = 1"
| "size (NEq _ _) = 1"
| "size (SepConj f1 f2) = size f1 + size f2 + 1"
| "size (Septraction f1 f2) = size f1 + size f2 + 1"
| "size (Conj f1 f2) = size f1 + size f2 + 1"
| "size (Disj f1 f2) = size f1 + size f2 + 1"
| "size (Neg f) = size f + 1"

fun atom :: "form \<Rightarrow> bool" where
  "atom Emp = True"
| "atom (PointsTo _ _) = True"
| "atom (LS _) = True"
| "atom (Eq _ _) = True"
| "atom (NEq _ _) = True"
| "atom _ = False"

fun fvs :: "form \<Rightarrow> var fset" where
  "fvs Emp = {||}"
| "fvs (PointsTo x y) = {|x,y|}"
| "fvs (LS (x,y)) = {|x,y|}"
| "fvs (Eq x y) = {|x,y|}"
| "fvs (NEq x y) = {|x,y|}"
| "fvs (SepConj P Q) = fvs P |\<union>| fvs Q"
| "fvs (Septraction P Q) = fvs P |\<union>| fvs Q"
| "fvs (Conj P Q) = fvs P |\<union>| fvs Q"
| "fvs (Disj P Q) = fvs P |\<union>| fvs Q"
| "fvs (Neg P) = fvs P"

type_synonym loc = nat
type_synonym stack = "var \<rightharpoonup> loc"
type_synonym heap = "loc \<rightharpoonup> loc"

text \<open>Models for SSL, cf. symbolic heap fragment.\<close>
typedef model =
  "{(s::stack,h::heap) |s h. finite (dom s) \<and> finite (dom h) \<and> (\<exists>l. s Nil = Some l \<and> l \<notin> dom h)}"
  \<comment> \<open>If stack or heap would be a fmap, setup_lifting would break, so we hardcode the finite domain.\<close>
proof -
  define m :: "(stack\<times>heap)" where "m \<equiv> ([Nil\<mapsto>0],Map.empty)"
  then have "m \<in> {(s, h) |s h. finite (dom s)  \<and> finite (dom h) \<and> (\<exists>l. s var.Nil = Some l \<and> l \<notin> dom h)}"
    by simp
  then show ?thesis ..
qed

setup_lifting type_definition_model
lemmas [simp] = Rep_model_inverse Rep_model_inject
lemmas [simp, intro!] = Rep_model[unfolded mem_Collect_eq]

lift_definition stack :: "model \<Rightarrow> stack" is fst .
lift_definition heap :: "model \<Rightarrow> heap" is snd .

definition locs :: "heap \<Rightarrow> loc set" where
  "locs h = dom h \<union> ran h"
definition dangling :: "loc \<Rightarrow> heap \<Rightarrow> bool" where
  "dangling l h = (l \<in> (ran h - dom h))"

text \<open>Weak heap union\<close>
definition weak_heap_union :: "heap \<Rightarrow> heap \<Rightarrow> heap option" (infix "++" 60) where
  "h1 ++ h2 = (if dom h1 \<inter> dom h2 = {} then Some (h1 ++ h2) else None)"

lemma weak_heap_union_sym: "(((h1::heap) ++ h2)::heap option) = (h2 ++ h1)"
  unfolding weak_heap_union_def by (auto simp: map_add_comm)

text \<open>Strong heap union\<close>
definition heap_union :: "heap \<Rightarrow> stack \<Rightarrow> heap \<Rightarrow> heap option" ("_ \<uplus>\<^sup>_ _") where
  "h1 \<uplus>\<^sup>s h2 = (if (dom h1 \<inter> ran h2) \<union> (dom h2 \<inter> ran h1) \<subseteq> ran s then h1 ++ h2 else None)"

lemma heap_union_sym: "h1 \<uplus>\<^sup>s h2 = h2 \<uplus>\<^sup>s h1"
  unfolding heap_union_def by (auto simp: weak_heap_union_sym)
lemma heap_union_sym_impl: "x = h1 \<uplus>\<^sup>s h2 \<Longrightarrow> x = h2 \<uplus>\<^sup>s h1"
  by (auto simp: heap_union_sym)  
  
lemma heap_union_model: "\<lbrakk>heap m = h; stack m = s; Some h = h1 \<uplus>\<^sup>s h2\<rbrakk> \<Longrightarrow> (s,h1) \<in> 
  {(s::stack,h::heap) |s h. finite (dom s) \<and> finite (dom h) \<and> (\<exists>l. s Nil = Some l \<and> l \<notin> dom h)}"
  apply transfer apply (auto simp: heap_union_def weak_heap_union_def)
  apply (metis dom_map_add finite_Un option.discI option.inject weak_heap_union_def)
  by (metis UnCI domIff dom_map_add option.discI option.inject weak_heap_union_def)

lemma heap_union_model': 
  "\<lbrakk>heap m = h; stack m = s; s Nil = Some l; Some h2 = h \<uplus>\<^sup>s h1; l \<notin> dom h1; finite (dom h1)\<rbrakk> 
  \<Longrightarrow> (s,h2) \<in> {(s::stack,h::heap) |s h. finite (dom s) \<and> finite (dom h) \<and> (\<exists>l. s Nil = Some l \<and> l \<notin> dom h)}"
  apply transfer apply (auto simp: heap_union_def weak_heap_union_def)
  apply (metis dom_map_add finite_UnI option.discI option.inject snd_eqD weak_heap_union_def)
  by (metis UnE domIff dom_map_add option.distinct(1) option.inject snd_eqD weak_heap_union_def)
  
subsection \<open>Semantics\<close>
fun list_segment :: "heap \<Rightarrow> loc \<Rightarrow> loc \<Rightarrow> nat \<Rightarrow> bool" where
  "list_segment _ _ _ 0 = False"
| "list_segment h l1 l2 (Suc 0) = (h = [l1\<mapsto>l2])"
| "list_segment h l1 l2 (Suc n) = (\<exists>h' l1'. h=h'++[l1\<mapsto>l1'] \<and> l1 \<notin> dom h' \<and> list_segment h' l1' l2 n)"

fun satisfies :: "(stack\<times>heap) \<Rightarrow> form \<Rightarrow> bool" where
  "satisfies (s,h) Emp = (dom h = {})"
| "satisfies (s,h) (x=\<^sub>sy) = (dom h = {} \<and> (\<exists>x' y'. s x = Some x' \<and> s y = Some y' \<and> x'=y'))"
| "satisfies (s,h) (x\<noteq>\<^sub>sy) = (dom h = {} \<and> (\<exists>x' y'. s x = Some x' \<and> s y = Some y' \<and> x'\<noteq>y'))"
| "satisfies (s,h) (x\<mapsto>\<^sub>sy) = (\<exists>x' y'. s x = Some x' \<and> s y = Some y' \<and> h = [x'\<mapsto>y'])"
| "satisfies (s,h) (ls (x,y)) = (\<exists>lx ly. s x = Some lx \<and> s y = Some ly \<and> 
    ((dom h = {} \<and> lx=ly) \<or> (\<exists>n. list_segment h lx ly n)))"
| "satisfies (s,h) (\<phi>1 \<and>\<^sub>s \<phi>2) = (satisfies (s,h) \<phi>1 \<and> satisfies (s,h) \<phi>2)"
| "satisfies (s,h) (\<phi>1 \<or>\<^sub>s \<phi>2) = (satisfies (s,h) \<phi>1 \<or> satisfies (s,h) \<phi>2)"
| "satisfies (s,h) (\<not>\<^sub>s \<phi>) = Not (satisfies (s,h) \<phi>)"
| "satisfies (s,h) (\<phi>1 \<^emph> \<phi>2) = 
  (\<exists>h1 h2. Some h = (h1 \<uplus>\<^sup>s h2) \<and> satisfies (s,h1) \<phi>1 \<and> satisfies (s,h2) \<phi>2)"
| "satisfies (s,h) (\<phi>1 -\<otimes> \<phi>2) = (\<exists>h1 h2. finite (dom h1) \<and> (\<exists>l. s Nil = Some l \<and> l \<notin> dom h1) \<and>
  satisfies (s,h1) \<phi>1 \<and> (h \<uplus>\<^sup>s h1) = Some h2 \<and> satisfies (s,h2) \<phi>2)"

lift_definition satisfies_model :: "model \<Rightarrow> form \<Rightarrow> bool" (infix "\<Turnstile>" 51) is satisfies .

fun weak_satisfies :: "(stack\<times>heap) \<Rightarrow> form \<Rightarrow> bool" where
  "weak_satisfies (s,h) (\<phi>1 \<^emph> \<phi>2) = 
  (\<exists>h1 h2. Some h = (weak_heap_union h1 h2) \<and> weak_satisfies (s,h1) \<phi>1 \<and> weak_satisfies (s,h2) \<phi>2)"
| "weak_satisfies (s,h) (\<phi>1 -\<otimes> \<phi>2) = 
  (\<exists>h1 h2. weak_satisfies (s,h1) \<phi>1 \<and> (h ++ h1) = Some h2 \<and> weak_satisfies (s,h2) \<phi>2)"
| "weak_satisfies (s,h) (\<phi>1 \<and>\<^sub>s \<phi>2) = (weak_satisfies (s,h) \<phi>1 \<and> weak_satisfies (s,h) \<phi>2)"
| "weak_satisfies (s,h) (\<phi>1 \<or>\<^sub>s \<phi>2) = (weak_satisfies (s,h) \<phi>1 \<or> weak_satisfies (s,h) \<phi>2)"
| "weak_satisfies (s,h) (\<not>\<^sub>s \<phi>) = Not (weak_satisfies (s,h) \<phi>)"
(*It's the same for the atoms.*)
| "weak_satisfies (s,h) \<phi> = satisfies (s,h) \<phi>" 

lift_definition weak_satisfies_model :: "model \<Rightarrow> form \<Rightarrow> bool" (infix "\<Turnstile>\<^sub>w" 51) is weak_satisfies .

lemma weak_strong_atoms: "atom P \<Longrightarrow> satisfies (s,h) P \<longleftrightarrow> weak_satisfies (s,h) P"
  by (induction P) auto
lemma weak_strong_watom_model: "atom P \<Longrightarrow> m \<Turnstile> P \<longleftrightarrow> m \<Turnstile>\<^sub>w P"
  apply transfer' using weak_strong_atoms by fast  
end
