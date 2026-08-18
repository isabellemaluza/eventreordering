theory JSHeapWF
imports JSDOM
begin

(* ==========================================================================
   Heap Well-Formedness Invariant
   ========================================================================== *)

definition distinct_heap_ids :: "heap => bool" where
  "distinct_heap_ids h = distinct (map fst h)"

lemma distinct_heap_ids_empty:
  "distinct_heap_ids []"
  by (simp add: distinct_heap_ids_def)

lemma distinct_heap_ids_Cons:
  "distinct_heap_ids ((k, v) # h) =
   (k ~: set (map fst h) & distinct_heap_ids h)"
  by (simp add: distinct_heap_ids_def)

lemma distinct_heap_ids_append:
  "distinct_heap_ids (h1 @ h2) =
   (distinct_heap_ids h1 &
    distinct_heap_ids h2 &
    set (map fst h1) Int set (map fst h2) = {})"
  by (auto simp: distinct_heap_ids_def)


(* ==========================================================================
   Main invariant
   ========================================================================== *)

definition heap_wf :: "js_state => bool" where
  "heap_wf s = distinct_heap_ids (Heap_s s)"


(* ==========================================================================
   Maximum heap identifier
   ========================================================================== *)

lemma max_heap_id_upper:
  "x : set (map fst h) ==> x <= max_heap_id h"
proof (induct h arbitrary: x)
  case Nil
  then show ?case
    by simp
next
  case (Cons a h)

  obtain k v where A [simp]: "a = (k, v)"
    by (cases a)

  from Cons.prems
  have X:
    "x = k | x : set (map fst h)"
    by simp

  then show ?case
  proof
    assume XK: "x = k"
    then show ?thesis
      by simp
  next
    assume XH: "x : set (map fst h)"

    have IH:
      "x <= max_heap_id h"
      using Cons.hyps XH
      by blast

    have U:
      "max_heap_id h <= max k (max_heap_id h)"
      by simp

    have
      "x <= max k (max_heap_id h)"
      using IH U
      by (rule order_trans)

    then show ?thesis
      by simp
  qed
qed


lemma max_heap_id_fresh:
  "max_heap_id h + 1 ~: set (map fst h)"
proof
  assume A:
    "max_heap_id h + 1 : set (map fst h)"

  have
    "max_heap_id h + 1 <= max_heap_id h"
    using max_heap_id_upper[OF A] .

  then show False
    by simp
qed


(* ==========================================================================
   Helper lemmas for filtered association lists
   ========================================================================== *)

lemma distinct_map_fst_filter:
  assumes D:
    "distinct (map fst h)"
  shows
    "distinct (map fst (filter P h))"
  using D
proof (induct h)
  case Nil
  then show ?case
    by simp
next
  case (Cons a h)

  obtain k v where A [simp]: "a = (k, v)"
    by (cases a)

  from Cons.prems
  have KN:
    "k ~: set (map fst h)"
    and DH:
    "distinct (map fst h)"
    by simp_all

  have IH:
    "distinct (map fst (filter P h))"
    using Cons.hyps DH
    by blast

  have KNF:
    "k ~: set (map fst (filter P h))"
  proof
    assume K:
      "k : set (map fst (filter P h))"

    from K have
      "k : set (map fst h)"
      by auto

    with KN show False
      by contradiction
  qed

  show ?case
  proof (cases "P a")
    case True
    then show ?thesis
      using IH KNF
      by simp
  next
    case False
    then show ?thesis
      using IH
      by simp
  qed
qed


lemma obj_id_notin_filtered_fst:
  "obj_id ~:
   set (map fst
     (filter (%(k,_). k ~= obj_id) h))"
  by (induct h) auto


(* ==========================================================================
   Allocation freshness
   ========================================================================== *)

lemma alloc_object_fresh:
  "fst (alloc_object props s) ~:
   set (map fst (Heap_s s))"
proof -
  have E:
    "fst (alloc_object props s) =
     max_heap_id (Heap_s s) + 1"
    by (simp add: alloc_object.simps)

  show ?thesis
    using E max_heap_id_fresh[of "Heap_s s"]
    by simp
qed


lemma alloc_dom_element_fresh:
  "fst (alloc_dom_element tag props s) ~:
   set (map fst (Heap_s s))"
proof -
  have E:
    "fst (alloc_dom_element tag props s) =
     max_heap_id (Heap_s s) + 1"
    by (simp add: alloc_dom_element.simps)

  show ?thesis
    using E max_heap_id_fresh[of "Heap_s s"]
    by simp
qed


(* ==========================================================================
   Allocation preserves well-formedness
   ========================================================================== *)

lemma alloc_object_preserves_wf:
  assumes WF:
    "heap_wf s"
  shows
    "heap_wf (snd (alloc_object props s))"
proof -
  from WF have D:
    "distinct_heap_ids (Heap_s s)"
    by (simp add: heap_wf_def)

  have F:
    "fst (alloc_object props s) ~:
     set (map fst (Heap_s s))"
    by (rule alloc_object_fresh)

  have H:
    "Heap_s (snd (alloc_object props s)) =
     (fst (alloc_object props s), VObject props) #
       Heap_s s"
    by (simp add: alloc_object.simps)

  show ?thesis
    unfolding heap_wf_def H
    using D F
    by (simp add: distinct_heap_ids_Cons)
qed


lemma alloc_dom_element_preserves_wf:
  assumes WF:
    "heap_wf s"
  shows
    "heap_wf (snd (alloc_dom_element tag props s))"
proof -
  from WF have D:
    "distinct_heap_ids (Heap_s s)"
    by (simp add: heap_wf_def)

  have F:
    "fst (alloc_dom_element tag props s) ~:
     set (map fst (Heap_s s))"
    by (rule alloc_dom_element_fresh)

  have H:
    "Heap_s (snd (alloc_dom_element tag props s)) =
     (fst (alloc_dom_element tag props s),
      VDOMElement tag props) #
       Heap_s s"
    by (simp add: alloc_dom_element.simps)

  show ?thesis
    unfolding heap_wf_def H
    using D F
    by (simp add: distinct_heap_ids_Cons)
qed


(* ==========================================================================
   Write / remove preserve well-formedness
   ========================================================================== *)

lemma write_object_preserves_distinct_ids:
  assumes D:
    "distinct_heap_ids (Heap_s s)"
  shows
    "distinct_heap_ids
       (Heap_s (write_object obj_id v s))"
proof -
  from D have D0:
    "distinct (map fst (Heap_s s))"
    by (simp add: distinct_heap_ids_def)

  have DF:
    "distinct
       (map fst
         (filter (%(k,_). k ~= obj_id)
           (Heap_s s)))"
    using distinct_map_fst_filter[OF D0] .

  have NI:
    "obj_id ~:
       set
        (map fst
          (filter (%(k,_). k ~= obj_id)
            (Heap_s s)))"
    by (rule obj_id_notin_filtered_fst)

  show ?thesis
    unfolding write_object.simps
              distinct_heap_ids_def
    using DF NI
    by simp
qed


lemma write_object_preserves_wf:
  assumes WF:
    "heap_wf s"
  shows
    "heap_wf (write_object obj_id v s)"
  using WF
  unfolding heap_wf_def
  by (rule write_object_preserves_distinct_ids)


lemma write_dom_element_preserves_wf:
  assumes WF:
    "heap_wf s"
  shows
    "heap_wf
       (write_dom_element obj_id tag props s)"
proof -
  have W:
    "heap_wf
       (write_object obj_id
         (VDOMElement tag props) s)"
    using write_object_preserves_wf[OF WF] .

  show ?thesis
    using W
    by (simp add: write_dom_element.simps)
qed


lemma remove_object_preserves_distinct_ids:
  assumes D:
    "distinct_heap_ids (Heap_s s)"
  shows
    "distinct_heap_ids
       (Heap_s (remove_object obj_id s))"
proof -
  from D have D0:
    "distinct (map fst (Heap_s s))"
    by (simp add: distinct_heap_ids_def)

  have DF:
    "distinct
       (map fst
         (filter (%(k,_). k ~= obj_id)
           (Heap_s s)))"
    using distinct_map_fst_filter[OF D0] .

  show ?thesis
    unfolding remove_object.simps
              distinct_heap_ids_def
    using DF
    by simp
qed


lemma remove_object_preserves_wf:
  assumes WF:
    "heap_wf s"
  shows
    "heap_wf (remove_object obj_id s)"
  using WF
  unfolding heap_wf_def
  by (rule remove_object_preserves_distinct_ids)


(* ==========================================================================
   Initial state
   ========================================================================== *)

lemma browser_init_state_wf:
  "heap_wf browser_init_state"
  by (simp add:
      heap_wf_def
      distinct_heap_ids_def
      browser_init_state_def)


(* ==========================================================================
   DOM construction preserves the invariant
   ========================================================================== *)

lemma build_dom_node_preserves_wf:
  assumes WF:
    "heap_wf s"
  shows
    "heap_wf (snd (build_dom_node n s))"
  using WF
  by (cases n;
      simp only: build_dom_node.simps Let_def;
      rule alloc_dom_element_preserves_wf;
      assumption)


lemma build_dom_list_preserves_wf:
  assumes WF:
    "heap_wf s"
  shows
    "heap_wf (build_dom_list ns s)"
  using WF
proof (induct ns arbitrary: s)
  case Nil
  then show ?case
    by simp
next
  case (Cons n ns)

  obtain id s' where B:
    "build_dom_node n s = (id, s')"
    by (cases "build_dom_node n s") auto

  have WN:
    "heap_wf (snd (build_dom_node n s))"
    using Cons.prems
    by (rule build_dom_node_preserves_wf)

  have WS:
    "heap_wf s'"
    using WN B
    by simp

  have WR:
    "heap_wf (build_dom_list ns s')"
    using Cons.hyps WS
    by blast

  show ?case
    using B WR
    by (simp add: build_dom_list.simps)
qed


(* ==========================================================================
   dom_state is well-formed
   ========================================================================== *)

lemma dom_state_wf:
  "heap_wf dom_state"
proof -
  have INIT:
    "heap_wf browser_init_state"
    by (rule browser_init_state_wf)

  have DOM:
    "heap_wf
       (build_dom_list sample_html browser_init_state)"
    using build_dom_list_preserves_wf[OF INIT] .

  show ?thesis
    using DOM
    by (simp add: dom_state_def)
qed

end