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
abbreviation magic_wand :: "form \<Rightarrow> form \<Rightarrow> form" (infix "-\<^emph>" 60) where 
  "magic_wand P Q \<equiv> \<not>\<^sub>s(P-\<otimes>\<not>\<^sub>sQ)"

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

lemma weak_heap_unionE: "h1 ++ h2 = Some h \<Longrightarrow> (dom h1 \<inter> dom h2 = {}) \<and> h=h1++h2"
  apply (auto simp: weak_heap_union_def)
  apply (metis disjoint_iff insertI1 insert_dom option.distinct(1))
  by (metis option.discI option.inject)

text \<open>Strong heap union\<close>
definition heap_union :: "heap \<Rightarrow> stack \<Rightarrow> heap \<Rightarrow> heap option" ("_ \<uplus>\<^sup>_ _") where
  "h1 \<uplus>\<^sup>s h2 = (if (dom h1 \<inter> ran h2) \<union> (dom h2 \<inter> ran h1) \<subseteq> ran s then h1 ++ h2 else None)"

lemma heap_union_sym: "h1 \<uplus>\<^sup>s h2 = h2 \<uplus>\<^sup>s h1"
  unfolding heap_union_def by (auto simp: weak_heap_union_sym)
lemma heap_union_sym_impl: "x = h1 \<uplus>\<^sup>s h2 \<Longrightarrow> x = h2 \<uplus>\<^sup>s h1"
  by (auto simp: heap_union_sym)
lemma heap_unionE: "h1 \<uplus>\<^sup>s h2 = Some h \<Longrightarrow> ((dom h1 \<inter> ran h2) \<union> (dom h2 \<inter> ran h1) \<subseteq> ran s) \<and>
  (dom h1 \<inter> dom h2 = {}) \<and> h=h1++h2"
  apply (auto simp: heap_union_def weak_heap_unionE)
  apply (meson IntI domI in_mono option.distinct(1))
  apply (meson IntI domI in_mono option.distinct(1))
  apply (metis disjoint_iff domIff option.distinct(1) weak_heap_union_def)
  by (metis option.inject option.simps(3) weak_heap_union_def)
  
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
fun list_segment :: "nat \<Rightarrow> heap \<Rightarrow> loc \<Rightarrow> loc \<Rightarrow> bool" where
  "list_segment 0 _ _ _ = False"
| "list_segment (Suc 0) h l1 l2 = (h = [l1\<mapsto>l2])"
| "list_segment (Suc n) h l1 l2 = (\<exists>h' l1'. h=h'++[l1\<mapsto>l1'] \<and> l1\<notin>dom h' \<and> list_segment n h' l1' l2)"

fun satisfies :: "(stack\<times>heap) \<Rightarrow> form \<Rightarrow> bool" where
  "satisfies (s,h) Emp = (dom h = {})"
| "satisfies (s,h) (x=\<^sub>sy) = (dom h = {} \<and> (\<exists>x' y'. s x = Some x' \<and> s y = Some y' \<and> x'=y'))"
| "satisfies (s,h) (x\<noteq>\<^sub>sy) = (dom h = {} \<and> (\<exists>x' y'. s x = Some x' \<and> s y = Some y' \<and> x'\<noteq>y'))"
| "satisfies (s,h) (x\<mapsto>\<^sub>sy) = (\<exists>x' y'. s x = Some x' \<and> s y = Some y' \<and> h = [x'\<mapsto>y'])"
| "satisfies (s,h) (ls (x,y)) = (\<exists>lx ly. s x = Some lx \<and> s y = Some ly \<and> 
    ((dom h = {} \<and> lx=ly) \<or> (\<exists>n. list_segment n h lx ly)))"
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

definition ssl_sat :: "var set \<Rightarrow> form \<Rightarrow> bool" where
  "ssl_sat x \<phi> \<equiv> \<exists>s h. x=dom s \<and> satisfies (s,h) \<phi>"
definition ssl_entails :: "form \<Rightarrow> var set \<Rightarrow> form \<Rightarrow> bool" ("_ \<turnstile>\<^sub>_ _") where
  "\<phi> \<turnstile>\<^sub>x \<psi> \<equiv> \<forall>s h. x=dom s \<and> satisfies (s,h) \<phi> \<longrightarrow> satisfies (s,h) \<psi>"

fun positive :: "form \<Rightarrow> bool" where
  "positive (P \<^emph> Q) = (positive P \<and> positive Q)"
| "positive (P -\<otimes> Q) = (positive P \<and> positive Q)"
| "positive (P\<and>\<^sub>sQ) = (positive P \<and> positive Q)"
| "positive (P\<or>\<^sub>sQ) = (positive P \<and> positive Q)"
| "positive (\<not>\<^sub>s _) = False"
| "positive _ = True"

lemma list_segment_semantics: "list_segment n h l1 l2 \<Longrightarrow> l1 \<in> dom h \<and> l2 \<in> ran h \<and> 
    (\<forall>l. (\<exists>x y. x\<noteq>y \<and> h x = Some l \<and> h y = Some l) \<longrightarrow> l=l2)
    \<and> ran h - dom h \<subseteq> {l2} \<and> dom h - ran h \<subseteq> {l1}
    \<and> (l1\<in>ran h \<longrightarrow> l1=l2)"
proof (induction n h l1 l2 rule: list_segment.induct)
  case (1 uu uv uw)
  then show ?case by simp
next
  case (2 h l1 l2)
  then have "h = [l1\<mapsto>l2]" by simp
  then show ?case by (auto simp: ran_def)
next
  case (3 v h l1 l2)
  then obtain h' l1' where h': "h=h'++[l1\<mapsto>l1']" "l1 \<notin> dom h'" "list_segment (Suc v) h' l1' l2" 
    by auto
  from h'(1,2) have dom_ran: "dom h = dom h' \<union> {l1}" "ran h = ran h' \<union> {l1'}" by auto
  {
    fix l
    assume "(\<exists>x y. x \<noteq> y \<and> h x = Some l \<and> h y = Some l)"
    then obtain x y where xy: "x \<noteq> y \<and> h x = Some l \<and> h y = Some l" by auto
    with 3(1)[OF h'(3)] h'(1,2) have "x \<in> dom h' \<and> y \<in> dom h' \<Longrightarrow> h' x = Some l \<and> h' y = Some l" 
      by (metis fun_upd_apply map_add_empty map_add_upd)
    with 3(1)[OF h'(3)] xy have both: "x \<in> dom h' \<and> y \<in> dom h' \<Longrightarrow> l = l2" by auto
    from xy 3(1)[OF h'(3)] h'(1,2) have l_l1':"\<not>(x \<in> dom h' \<and> y \<in> dom h') \<Longrightarrow> l = l1'"
      by auto (metis option.inject)+
    moreover from xy h'(1) have "\<not>(x \<in> dom h' \<and> y \<in> dom h') \<Longrightarrow> x\<in>dom h' \<or>y\<in>dom h'" 
      apply auto apply (metis option.distinct(1)) by (metis option.distinct(1))
    ultimately have "\<not>(x \<in> dom h' \<and> y \<in> dom h') \<Longrightarrow> l1' \<in> ran h'" using xy h'(1) apply auto
      apply (smt (verit, best)  map_add_empty map_add_upd map_upd_Some_unfold ranI) by (metis ranI)
    with 3(1)[OF h'(3)] have "\<not>(x \<in> dom h' \<and> y \<in> dom h') \<Longrightarrow> l1' = l2" by simp
    with l_l1' have "\<not>(x \<in> dom h' \<and> y \<in> dom h') \<Longrightarrow> l=l2" by simp
    with both have "l=l2" by auto
  }  
  then have "\<forall>l. (\<exists>x y. x \<noteq> y \<and> h x = Some l \<and> h y = Some l) \<longrightarrow> l = l2" by simp
  moreover from dom_ran 3(1)[OF h'(3)] have "l1 \<in> dom h" "l2 \<in> ran h" by auto
  moreover from dom_ran 3(1)[OF h'(3)] have "ran h - dom h \<subseteq> {l2}" by auto
  moreover from dom_ran 3(1)[OF h'(3)] have "dom h - ran h \<subseteq> {l1}" by auto
  moreover from dom_ran 3(1)[OF h'(3)] have "l1 \<in> ran h \<longrightarrow> l1 = l2" using h'(2) by auto
  ultimately show ?case by simp
qed

lemma positive_var_locations:
assumes "positive \<phi>" "weak_satisfies (s,h) \<phi>"
shows "(ran h - dom h \<subseteq> ran s) \<and> (\<forall>l. (\<exists>x y. x\<noteq>y \<and> h x = Some l \<and> h y = Some l) \<longrightarrow> l \<in> ran s) \<and>
  (dom h - ran h \<subseteq> ran s)"
using assms proof (induction \<phi> arbitrary: s h)
case Emp
  then have "h=Map.empty" by auto
  then have "ran h = {}" "dom h = {}" "\<forall>x. h x = None" by auto
  then show ?case by auto
next
  case (PointsTo x1 x2)
  then obtain y1 y2 where s: "s x1 = Some y1" "s x2 = Some y2" by auto
  with PointsTo have "h=[y1\<mapsto>y2]" by simp
  with s show ?case apply auto
    apply (smt (verit, ccfv_SIG) mem_Collect_eq option.simps(3) ran_def)
    by (metis option.discI ranI)
next
  case (LS x)
  obtain x1 x2 where "x=(x1,x2)" by fastforce
  with LS(2) obtain y1 y2 where y12: "s x1 = Some y1" "s x2 = Some y2" 
    "((dom h = {} \<and> y1=y2) \<or> (\<exists>n. list_segment n h y1 y2))" by fastforce
  moreover { 
    assume "\<exists>n. list_segment n h y1 y2"
    then obtain n where "list_segment n h y1 y2" by auto
    then have "y1 \<in> dom h \<and> y2 \<in> ran h \<and> (\<forall>l. (\<exists>x y. x \<noteq> y \<and> h x = Some l \<and> h y = Some l) \<longrightarrow> l = y2) 
      \<and> ran h - dom h \<subseteq> {y2} \<and> dom h - ran h \<subseteq> {y1} \<and> (y1 \<in> ran h \<longrightarrow> y1 = y2)" using list_segment_semantics
      by simp
    with y12 have ?case by (auto intro: ranI)
  } 
  moreover have "dom h = {} \<and> y1=y2 \<Longrightarrow> ?case" by simp
  ultimately show ?case by blast
next
  case (Eq x1 x2)
  then have "h=Map.empty" by auto
  then have "ran h = {}" "dom h = {}" "\<forall>x. h x = None" by auto
  then show ?case by auto
next
  case (NEq x1 x2)
  then have "h=Map.empty" by auto
  then have "ran h = {}" "dom h = {}" "\<forall>x. h x = None" by auto
  then show ?case by auto
next
  case (SepConj \<phi>1 \<phi>2)
  then obtain h1 h2 where h12: "h1 ++ h2 = Some h" "weak_satisfies (s,h1) \<phi>1" "weak_satisfies (s,h2) \<phi>2"
    by auto
  from SepConj(3) have pos: "positive \<phi>1" "positive \<phi>2" by simp_all
  from weak_heap_unionE[OF h12(1)] have "dom h1 \<inter> dom h2 = {}" "dom h = dom h1 \<union> dom h2" "ran h = ran h1 \<union> ran h2"
    by (auto simp: weak_heap_union_def ran_map_add)
  with SepConj(1)[OF pos(1) h12(2)] SepConj(2)[OF pos(2) h12(3)] show ?case apply auto
    by (smt (verit) Diff_iff \<open>dom h1 \<inter> dom h2 = {} \<and> h = h1 ++ h2\<close> disjoint_iff in_mono map_add_Some_iff ranI)  
next
  case (Septraction \<phi>1 \<phi>2)
  then obtain h0 h1 where h01: "Some h1 = h0++h" "weak_satisfies (s,h0) \<phi>1" "weak_satisfies (s,h1) \<phi>2"
    by auto (metis weak_heap_union_sym)
  from Septraction(3) have pos: "positive \<phi>1" "positive \<phi>2" by simp_all
  from weak_heap_unionE[OF h01(1)[symmetric]] have dom_ran: "dom h0 \<inter> dom h = {}" "dom h1 = dom h0 \<union> dom h"
    "ran h1 = ran h \<union> ran h0" by (auto simp: ran_map_add)
  then have join: "(\<exists>x y. x\<noteq>y \<and> h x = Some l \<and> h y = Some l) \<longrightarrow> (\<exists>x y. x\<noteq>y \<and> h1 x = Some l \<and> h1 y = Some l)" for l
    by auto (metis \<open>dom h0 \<inter> dom h = {} \<and> h1 = h0 ++ h\<close> map_add_find_right)
  \<comment> \<open>For a dangling pointer l in h, it is either also dangling in h1 or a join point in h1 
    or pointing to a source in h0.\<close>
  from dom_ran have "(h l = Some l' \<and> l' \<in> ran h - dom h) \<Longrightarrow> (l' \<in> ran h1 - dom h1 \<or> 
    (\<exists>x y. x\<noteq>y \<and> h1 x = Some l' \<and> h1 y = Some l') \<or> l' \<in> dom h0 - ran h0)" for l l'
    by auto (smt (verit, ccfv_threshold) \<open>dom h0 \<inter> dom h = {} \<and> h1 = h0 ++ h\<close> disjoint_iff domI 
      map_add_dom_app_simps(1) map_add_dom_app_simps(3) mem_Collect_eq ran_def)
  with Septraction(1)[OF pos(1) h01(2)] Septraction(2)[OF pos(2) h01(3)] join
  show ?case apply auto apply (smt (verit, ccfv_threshold) DiffI domD in_mono mem_Collect_eq ran_def)
  by (metis DiffI Un_iff \<open>dom h0 \<inter> dom h = {} \<and> h1 = h0 ++ h\<close> disjoint_iff domIff dom_map_add dom_ran(3) in_mono inf_sup_aci(5) option.distinct(1))
next
  case (Conj \<phi>1 \<phi>2)
  then have "weak_satisfies (s,h) \<phi>1" "weak_satisfies (s,h) \<phi>2" by auto
  from Conj(1)[OF _ this(1)] Conj(2)[OF _ this(2)] Conj(3) show ?case by auto
next
  case (Disj \<phi>1 \<phi>2)
  then have sat: "weak_satisfies (s,h) \<phi>1 \<or> weak_satisfies (s,h) \<phi>2" by auto
  from Disj(3) have "positive \<phi>1" "positive \<phi>2" by auto
  with sat Disj(1,2) show ?case by auto blast+
next
  case (Neg \<phi>)
  then show ?case by simp
qed

end
