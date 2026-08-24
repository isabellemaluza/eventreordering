# Formalization Audit — Event Independence and Reordering in JavaScript with Isabelle/HOL

**Audit date:** 2026-08-18
**Workspace:** `/Users/isamaluza/Documents/eventreordering`
**Object audited:** all Isabelle/HOL theory files in `Codes/` (14 actual `.thy` files; `*.thy~` backups ignored per instructions).
**Audit character:** static scientific audit. An independent Isabelle/HOL verification of the theories was executed non-destructively on copies during this audit; it completed successfully (see the Appendix at the end of this report for the exact commands and outcome).

> Legend used throughout:
> **DEFINED** — explicitly defined in Isabelle.
> **PROVED** — explicitly established by a theorem/lemma in the files (including proofs by normalization/`eval`).
> **DERIVED** — follows from existing proved results by simple combination (not itself mechanized).
> **INTERPRETATION** — scientific reading of a formal result.
> **NOT PROVED** — would require additional mechanization.

---

## 1. Executive Summary

The `Codes/` directory contains a coherent, layered Isabelle/HOL development (14 theories, ~2,800 lines) modeling a **simplified JavaScript/DOM execution environment**: an association-list heap, a `js_state` record (stack, heap, event queue field, alert log), a fuel-bounded evaluator, DOM elements as heap values (`VDOMElement`), a two-event-kind dispatch (`make_event_handler`), an HTML renderer (`tohtml`), and an observational-equivalence relation (`obs_equiv` = equal rendered HTML + equal alert history).

**What is genuinely mechanized and strong:**

- *Heap locality* (JSLocality.thy): operations on **distinct heap identifiers** do not interfere with each other's loads, and two writes to distinct identifiers **commute up to extensional heap equality** (`heap_ext_eq`, i.e., all `load_object` results agree). These are unconditional-in-structure results (single assumption: `i ≠ j`).
- *Event absorption* (JSAbsEvent.thy): events whose target is missing, is not a DOM element, or has no handler for that event kind leave the state **unchanged** (`make_event_handler ev obj s = s`), with observational consequences in JSObsEquiv.thy.
- *Write absorption / idempotence* (JSProofs.thy, JSFrameRule.thy): repeated color changes to the **same** element obey last-write-wins (`change_element_color_absorbs`), packaged observationally as `write_absorption_law`.
- *Observational-equivalence infrastructure* (JSObsEquiv.thy): `obs_equiv` is an equivalence relation; state equality implies it; absorption implies it.
- *Event-reordering theorems* (JSFrameRule.thy): `frame_rule_events`, `frame_rule_events_by_effect`, `events_reorder_two`, `events_reorder_two_by_effect` **exist and are proved** — but they are **conditional**: their hypotheses state (up to definitional unfolding) the very observational equivalence, or intermediate-state effect equalities that directly imply it, for the two execution orders.

**The central gap.** The chain suggested by the proposed abstract — *locality ⇒ independence ⇒ frame rule ⇒ commutativity ⇒ reordering ⇒ observational consequence* — is **only partially closed**:

1. There is **no theorem** of the form "two handlers that only change distinct DOM elements can be reordered without changing observable behavior." Event-handler independence (`make_event_handler` level) is **NOT PROVED**; only heap-operation independence is proved.
2. There is **no bridge lemma** connecting `heap_ext_eq` to `tohtml`/`obs_equiv` (verified by exhaustive grep: `heap_ext_eq` appears only in JSLocality.thy and in the two heap-level frame rules of JSFrameRule.thy).
3. The event-level "frame rules" and reordering theorems take `obs_equiv` of the two orders (or effect equations implying it) **as assumptions**. They are sound bookkeeping theorems, not independence criteria. JSFrameRule.thy's own header comments confirm this design.

**Consequence for the paper.** The strongest scientifically defensible claim today is about **heap-level locality, commutativity, and absorption**, plus **conditional event reordering**. The abstract's sentence that handlers acting on distinct parts of the state can be executed in different orders "sem alterar o resultado observável" (without changing the observable result) is **NOT CURRENTLY PROVED** and must be qualified, or the missing bridge results must be mechanized first (Section 19 classifies them as ESSENTIAL).

**Title.** "Formal Verification of Event Independence and Reordering in JavaScript with Isabelle/HOL" is classified **TOO BROAD** for the current mechanization (event-level independence is not proved; reordering is conditional). Alternatives are proposed in Section 14.

---

## 2. Scope of the Formalization

### 2.1 Files

14 actual `.thy` files in `Codes/` (backups `*.thy~` excluded):

| Theory | Lines | Imports | Role |
|---|---|---|---|
| `JSMemoryModel.thy` | 187 | `Complex_Main` | Base values, expressions, stack/heap/state, heap operations, `browser_init_state` |
| `JSHTMLSyntax.thy` | 28 | `JSMemoryModel` | Surface HTML/attribute syntax (`html_node`, `html_attr`) |
| `JSDOM.thy` | 65 | `JSHTMLSyntax` | DOM construction from HTML (`build_dom_list`, `sample_html`, `dom_state`) |
| `JSEval.thy` | 140 | `JSMemoryModel` | The official evaluator (`eval_expr_fuel`, `eval_expr`), builtins, `run_handler` |
| `JSEvents.thy` | 42 | `JSDOM`, `JSEval` | Event kinds, handler lookup and dispatch (`make_event_handler`) |
| `JSRender.thy` | 89 | `JSEvents` | Rendering: `tohtml`, `sample_pos` |
| `JSQuerySelector.thy` | 80 | `JSDOM` | CSS selector subset (`querySelector`, `querySelectorAll`), color-change wrappers |
| `JSAbsEvent.thy` | 190 | `JSRender`, `JSQuerySelector` | Event-absorption theorems and consequences |
| `JSHeapWF.thy` | 454 | `JSDOM` | Heap well-formedness (`heap_wf` = distinct ids), freshness, preservation |
| `JSLocality.thy` | 580 | `JSHeapWF` | **Locality**: load independence, `heap_ext_eq`, commutativity of distinct writes |
| `JSProofs.thy` | 109 | `JSRender`, `JSQuerySelector` | Idempotence, last-write-wins, insert/remove properties |
| `JSFuel.thy` | 122 | `JSEval` | Fuel lemmas, determinism (and an explicit note that fuel monotonicity is **not** established) |
| `JSObsEquiv.thy` | 280 | `JSRender`, `JSLocality`, `JSProofs`, `JSAbsEvent` | Observational equivalence (`observable`, `obs_equiv`) and consequences |
| `JSFrameRule.thy` | 461 | `JSObsEquiv`, `JSFuel` | **Frame rules and event reordering** (`run_events`, `frame_rule_*`, `events_reorder_*`) |

No `ROOT`/`ROOTS` session file is present in the workspace; the theories form a flat directory of name-imported files. No root theory imports `JSFrameRule` explicitly, but it transitively covers all 14 theories.

### 2.2 What the model contains (DEFINED)

- **Values** (`js_vle`): numbers (reals), NaN, booleans, strings, null, undefined, heap references (`VRef nat`), objects, window, DOM elements (`VDOMElement tag props`), functions (params/body/env), builtins, type errors.
- **Expressions** (`expr`): constants, variables, assignment, binary operators, calls, if, sequence, return.
- **State** (`js_state` record): `Stack_s` (lexical frames), `Heap_s` (association list `(nat * js_vle) list`), `Events_s` (`event_queue = (string * expr) list` — **declared but unused by the event machinery**), `Alerts_s` (alert history).
- **Builtins**: `BAlert`, `BChangeColor`, `BCreateElement`.
- **Events**: `js_event_kind = EvClick | EvMouseOver`; dispatch via `make_event_handler :: js_event_kind => nat => js_state => js_state`, which looks up `onclick`/`onmouseover` on the target `VDOMElement` and runs the handler with `this` bound to `VRef target_id`.
- **Observable behavior**: `observable s p = (tohtml s p, Alerts_s s)`; `obs_equiv s1 s2 p ⟺ tohtml s1 p = tohtml s2 p ∧ Alerts_s s1 = Alerts_s s2` (parameterized by a position map `p :: dom_pos`).
- **Locality relation**: `heap_ext_eq s1 s2 ⟺ (∀k. load_object k s1 = load_object k s2)`.
- **Event sequences**: `run_events :: (js_event_kind * nat) list => js_state => js_state`.

### 2.3 What the model does not contain

No event loop, no task/microtask queues, no promises, no asynchrony, no concurrency (dispatch is a synchronous total state transformer); no event bubbling/capture or event object; no CSS layout; no text/node mutation inside handlers beyond `alert`/`changeColor`/`createElement`; `Events_s` is never read or written by `make_event_handler`/`run_events`/the evaluator (grep confirms: `Events_s` occurs only in the record definition and `browser_init_state`).

---

## 3. Theory Dependency Map

```
JSMemoryModel.thy (Complex_Main)
 ├─ JSHTMLSyntax.thy
 │    └─ JSDOM.thy
 │         ├─ JSEvents.thy ────────────┐
 │         │    └─ JSRender.thy ───────┼──────────────────────────┐
 │         ├─ JSQuerySelector.thy ─────┤                          │
 │         │    └──────────────────────┼─ JSAbsEvent.thy ──┐      │
 │         ├─ JSHeapWF.thy             │                   │      │
 │         │    └─ JSLocality.thy ─────┼───────────────────┼──┐   │
 │         └─ JSProofs.thy (via JSRender, JSQuerySelector) ─┼──┤   │
 ├─ JSEval.thy                                                 │  │   │
 │    ├─ JSEvents.thy (with JSDOM) ──(see above)              │  │   │
 │    └─ JSFuel.thy ──────────────────────────────────────────┼──┼───┼──┐
 │                                                            │  │   │  │
 └─ JSObsEquiv.thy (imports JSRender, JSLocality, JSProofs, JSAbsEvent)
      └─ JSFrameRule.thy (imports JSObsEquiv, JSFuel)
```

Edges (verified from the `imports` clauses): `JSEval → JSMemoryModel`; `JSHTMLSyntax → JSMemoryModel`; `JSDOM → JSHTMLSyntax`; `JSEvents → JSDOM, JSEval`; `JSRender → JSEvents`; `JSQuerySelector → JSDOM`; `JSAbsEvent → JSRender, JSQuerySelector`; `JSHeapWF → JSDOM`; `JSLocality → JSHeapWF`; `JSProofs → JSRender, JSQuerySelector`; `JSFuel → JSEval`; `JSObsEquiv → JSRender, JSLocality, JSProofs, JSAbsEvent`; `JSFrameRule → JSObsEquiv, JSFuel`.

`JSFrameRule.thy` is the top of the dependency cone and transitively includes all 13 other theories.

---

## 4. Relevant Definitions

### 4.1 `JSMemoryModel.thy` (DEFINED)

- `datatype builtin = BAlert | BChangeColor | BCreateElement`
- `datatype js_vle = VNumber real | VNaN | VBool bool | VString string | VNull | VUndefined | VRef nat | VObject "(string*js_vle) list" | VWindow "(string*js_vle) list" | VDOMElement string "(string*js_vle) list" | VFunction "string list" expr "(string*js_vle) list" | VBuiltin builtin | VTypeError string` — mutually recursive with `expr = EConst js_vle | EVar string | EAssign string expr | EBinOp string expr expr | ECall expr "expr list" | EIf expr expr expr | ESeq expr expr | EReturn expr`.
- `type_synonym frame = "(string*js_vle) list"`; `stack = "frame list"`; `heap = "(nat*js_vle) list"`; `event = "string*expr"`; `event_queue = "event list"`.
- `record js_state = Stack_s :: stack | Heap_s :: heap | Events_s :: event_queue | Alerts_s :: "string list"`.
- Property access/update: `get_prop`, `update_prop`.
- Stack: `lookup_stack`, `load_var`, `update_in_frame`, `write_var`, `push_frame`, `pop_frame`.
- Heap: `load_object`, `load_global`, `max_heap_id`, `alloc_object`, `alloc_dom_element`, `write_object`, `remove_object`, `write_dom_element`, `write_window`, `insert_dom_element`, `change_element_color`.
- `browser_init_state` — canonical initial state: window at heap id 0 with the three builtins; empty stack/events/alerts.

### 4.2 `JSHTMLSyntax.thy` / `JSDOM.thy` (DEFINED)

- `html_attr = Attr string string | AttrOnClick expr | AttrOnMouseOver expr`; `html_node = HtmlText string | HtmlElement string "html_attr list" "html_node list"`.
- `attr_to_prop` maps `AttrOnClick e ↦ [("onclick", VFunction [] e [])]`, `AttrOnMouseOver e ↦ [("onmouseover", VFunction [] e [])]`.
- `build_dom_node`/`build_dom_list` build heap entries by `alloc_dom_element`; `sample_html` (a `<p id="msg" color="yellow">` and a `<button onclick="alert('Ola'); changeColor(this,'blue')">`); `dom_state = build_dom_list sample_html browser_init_state` (heap: id 0 window, id 1 paragraph, id 2 button).

### 4.3 `JSEval.thy` (DEFINED)

- `is_truthy`, `eval_binop` (`+` on numbers only; everything else → `VTypeError`).
- `eval_expr_fuel :: nat => expr => js_state => (js_vle * js_state)` / `eval_exprs_fuel` — fuel-bounded, total; builtins mutate the state directly (`alert` appends to `Alerts_s`; `changeColor` calls `change_element_color`; `createElement` allocates and returns `VRef`).
- `default_fuel = 200`; `eval_expr = eval_expr_fuel default_fuel`; `eval_exprs`.
- `run_handler target_id (VFunction params body clos_env) st` — pushes `clos_env @ [("this", VRef target_id)]`, evaluates the body, pops the frame; non-functions are a no-op.

### 4.4 `JSEvents.thy` (DEFINED)

- `js_event_kind = EvClick | EvMouseOver`; `prop_of_event EvClick = "onclick"`, `prop_of_event EvMouseOver = "onmouseover"`.
- `make_event_handler ev_kind target_id state` — loads `target_id`; if it is a `VDOMElement` with property `prop_of_event ev_kind`, runs it with `run_handler`; otherwise returns the state unchanged.

### 4.5 `JSRender.thy` (DEFINED)

- `dom_pos = (nat*nat) list`; `tohtml state pos = strip_pos (sort_by_pos (collect_dom_nodes (Heap_s state) pos))` — renders heap `VDOMElement`s into a flat `html_node list` ordered by the given positions; `sample_pos = build_pos sample_html 1 0`.

### 4.6 `JSQuerySelector.thy` (DEFINED)

- `selector` (tag/class/id/unsupported), `parse_selector`, `matches_selector`, `querySelector`, `querySelectorAll`, `JS_querySelector_blue`, `JS_querySelectorAll_yellow`, `demo_state`.

### 4.7 `JSHeapWF.thy` (DEFINED)

- `distinct_heap_ids h ⟺ distinct (map fst h)`; `heap_wf s ⟺ distinct_heap_ids (Heap_s s)`.

### 4.8 `JSLocality.thy` (DEFINED)

- `heap_ext_eq s1 s2 ⟺ (∀k. load_object k s1 = load_object k s2)` — **extensional heap equality** (all loads agree), an equivalence relation (`heap_ext_eq_refl/sym/trans`).

### 4.9 `JSObsEquiv.thy` (DEFINED)

- `observable s pos = (tohtml s pos, Alerts_s s)`; `obs_equiv s1 s2 p ⟺ tohtml s1 p = tohtml s2 p ∧ Alerts_s s1 = Alerts_s s2`.

### 4.10 `JSFrameRule.thy` (DEFINED)

- `run_events [] s = s`; `run_events ((ev,target)#rest) s = run_events rest (make_event_handler ev target s)`.

### 4.11 `JSFuel.thy` (DEFINED)

- `out_of_fuel v ⟺ v = VTypeError "Out of fuel"`; `eval_succeeds n e s ⟺ ¬ out_of_fuel (fst (eval_expr_fuel n e s))`.

---

## 5. Locality Results (JSLocality.thy)

**What "locality" means here (DEFINED + PROVED):** *extensional independence of heap operations over distinct heap identifiers* — an operation on identifier `j` never changes what a `load_object i` observes for any `i ≠ j`, and two operations on distinct identifiers commute up to `heap_ext_eq`. Locality is expressed **in terms of heap identifiers** (`nat`), not in terms of DOM elements or full states; DOM-element operations (`write_dom_element`, `change_element_color`) inherit locality because they are defined as heap writes.

### Load/write independence (PROVED)

- `load_object_write_same`: `load_object i (write_object i v s) = Some v`.
- `load_object_write_independent`: `i ≠ j ⟹ load_object i (write_object j v s) = load_object i s`.
- `load_object_remove_same`: `load_object i (remove_object i s) = None`.
- `load_object_remove_independent`: `i ≠ j ⟹ load_object i (remove_object j s) = load_object i s`.
- `load_object_write_dom_same`: `load_object i (write_dom_element i tag props s) = Some (VDOMElement tag props)`.
- `load_object_write_dom_independent`: `i ≠ j ⟹ load_object i (write_dom_element j tag props s) = load_object i s`.
- `load_object_change_color_independent`: `i ≠ j ⟹ load_object i (change_element_color j color s) = load_object i s` (proved by full case analysis over the stored value).
- Aliases (used as building blocks): `write_object_observational_independent`, `write_dom_element_observational_independent`, `change_element_color_observational_independent` — note these names are slightly misleading: they state **load equality**, not `obs_equiv`.

### Commutativity up to extensional heap equality (PROVED)

- `write_object_commute_load` (lemma): `i ≠ j ⟹ load_object k (write_object i vi (write_object j vj s)) = load_object k (write_object j vj (write_object i vi s))`.
- `write_object_commute_ext` (theorem): `i ≠ j ⟹ heap_ext_eq (write_object i vi (write_object j vj s)) (write_object j vj (write_object i vi s))`.
- `write_dom_element_commute_ext` (theorem): `i ≠ j ⟹ heap_ext_eq (write_dom_element i tag props (write_dom_element j tag' props' s)) (write_dom_element j tag' props' (write_dom_element i tag props s))`.

**Strongest locality results for the SIICUSP paper:** `write_object_commute_ext`, `write_dom_element_commute_ext`, and `load_object_change_color_independent` (the footprint property used by `frame_rule_change_color_load`).

**Caveats:** (i) the conclusion is `heap_ext_eq` — the two heaps are extensionally equal but **not list-equal** (entry order differs), and nothing connects `heap_ext_eq` to `tohtml`/`obs_equiv` in the development; (ii) no theorem covers `alloc_object`/`alloc_dom_element` interference beyond well-formedness (freshness is proved in JSHeapWF); (iii) there is **no** `make_event_handler`-level locality theorem.

---

## 6. Independence Results

The formalization contains **heap-operation independence**, not event/handler independence:

| Result | Theory | Assumptions | Conclusion | Kind |
|---|---|---|---|---|
| `load_object_write_independent` | JSLocality | `i ≠ j` | `load_object i (write_object j v s) = load_object i s` | load preservation |
| `load_object_remove_independent` | JSLocality | `i ≠ j` | `load_object i (remove_object j s) = load_object i s` | load preservation |
| `load_object_write_dom_independent` | JSLocality | `i ≠ j` | `load_object i (write_dom_element j tag props s) = load_object i s` | load preservation |
| `load_object_change_color_independent` | JSLocality | `i ≠ j` | `load_object i (change_element_color j color s) = load_object i s` | load preservation |
| `write_object_commute_ext` | JSLocality | `i ≠ j` | `heap_ext_eq (…i then j…) (…j then i…)` | extensional heap equality |
| `write_dom_element_commute_ext` | JSLocality | `i ≠ j` | `heap_ext_eq` of the two write orders | extensional heap equality |

**What independence is formalized:** two heap operations on distinct identifiers are mutually non-interfering (w.r.t. loads) and commute extensionally. **What is NOT formalized:** independence of *event handlers* (`make_event_handler` results), independence of *events*, or independence of arbitrary JavaScript programs. Distinctness of identifiers (`i ≠ j`) is the sole structural condition — there is no analysis of reachable cells or aliasing.

---

## 7. Frame Rule Results (JSFrameRule.thy)

### 7.1 Heap-level frame rules (PROVED, conditional on `i ≠ j` only)

- `frame_rule_write_object`: `i ≠ j ⟹ heap_ext_eq (write_object i vi (write_object j vj s)) (write_object j vj (write_object i vi s))` — a restatement of `write_object_commute_ext`.
- `frame_rule_write_dom_element`: same shape for `write_dom_element` (restatement of `write_dom_element_commute_ext`).
- `frame_rule_change_color_load`: `i ≠ j ⟹ load_object i (change_element_color j color s) = load_object i s` — the footprint of a color change.

These are the only results in the file whose hypothesis is the structural condition `i ≠ j`.

### 7.2 Event-level frame rules (PROVED, but conditional on observational hypotheses)

- `frame_rule_events`:
  - Assumptions: `LEFT: make_event_handler ev_j j (make_event_handler ev_i i s) = left_state`; `RIGHT: make_event_handler ev_i i (make_event_handler ev_j j s) = right_state`; `OBS: obs_equiv left_state right_state p`.
  - Conclusion: `obs_equiv (make_event_handler ev_j j (make_event_handler ev_i i s)) (make_event_handler ev_i i (make_event_handler ev_j j s)) p`.
  - Assessment: after unfolding `LEFT`/`RIGHT`, the conclusion *is* `OBS`. The theorem packages the hypothesis over named intermediate states; it provides **no criterion** for when `OBS` holds. There is no `i ≠ j` assumption.
- `frame_rule_events_by_effect`:
  - Assumptions: `HI: make_event_handler ev_i i (make_event_handler ev_j j s) = change_element_color i ci (make_event_handler ev_j j s)`; `HJ: make_event_handler ev_j j (make_event_handler ev_i i s) = change_element_color j cj (make_event_handler ev_i i s)`; `OBS: obs_equiv (change_element_color j cj (make_event_handler ev_i i s)) (change_element_color i ci (make_event_handler ev_j j s)) p`.
  - Conclusion: `obs_equiv` of the two handler-execution orders.
  - Assessment: hypotheses `HI`/`HJ` characterize each handler's effect **on the actual intermediate states** as a color change; again, unfolding `HI`/`HJ` makes the conclusion equal to `OBS`. This is the "useful form for proving concrete independent handlers" (per the file's comment) — but the independent-handler **instances themselves are never proved** in the development.

### 7.3 What the formalization calls a frame rule

A **frame rule** here means: (heap level) distinct-target operations commute extensionally, stated as theorems; (event level) theorems that transfer an observational-equivalence hypothesis about the two concrete executions into a conclusion about them, with optional effect characterizations. The event-level rules are **conditional** — they assume (essentially) what they conclude. The development does **not** use separation logic; describing these as separation-logic frame rules would be an overstatement. The file header explicitly states: *"We do not assume that an event handler is unaffected merely because a different heap cell was changed… event-level reordering uses explicit assumptions about the two intermediate executions."*

---

## 8. Event Reordering Results (JSFrameRule.thy)

### 8.1 Inventory

| Name | Exists? | Proved? | Shape |
|---|---|---|---|
| `frame_rule_events` | YES (line 110) | YES | conditional (assumes obs-equiv of the two orders) |
| `frame_rule_events_by_effect` | YES (line 139) | YES | conditional (effect equations + obs-equiv) |
| `events_reorder_two` | YES (line 177) | YES | conditional (assumes obs-equiv of the two orders) |
| `events_reorder_two_by_effect` | YES (line 198) | YES | conditional (intermediate-state equations + obs-equiv) |

### 8.2 Exact statements

- `events_reorder_two`:
  - Assumption `FRAME`: `obs_equiv (make_event_handler ev_j j (make_event_handler ev_i i s)) (make_event_handler ev_i i (make_event_handler ev_j j s)) p`.
  - Conclusion: `obs_equiv (run_events [(ev_i,i),(ev_j,j)] s) (run_events [(ev_j,j),(ev_i,i)] s) p`.
  - Proof: `using FRAME by simp` — unfolds `run_events_two`. The assumption is the conclusion modulo the definition of `run_events`.
- `events_reorder_two_by_effect`:
  - Assumptions: `HI: make_event_handler ev_i i (make_event_handler ev_j j s) = si`; `HJ: make_event_handler ev_j j (make_event_handler ev_i i s) = sj`; `OBS: obs_equiv sj si p`.
  - Conclusion: `obs_equiv (run_events [(ev_i,i),(ev_j,j)] s) (run_events [(ev_j,j),(ev_i,i)] s) p`.
  - Proof: `run_events [(ev_i,i),(ev_j,j)] s = sj` (via `HJ`), `run_events [(ev_j,j),(ev_i,i)] s = si` (via `HI`), then `OBS`.

### 8.3 Three-level explanation of the strongest reordering theorem

**Level 1 — Exact formal statement.** See `events_reorder_two_by_effect` above. Isabelle/HOL fact: from the two equation hypotheses naming the results `si`, `sj` of the two sequential compositions and the hypothesis `obs_equiv sj si p`, it follows that running the two-event sequences in either order yields states that are `obs_equiv` (same `tohtml` and same `Alerts_s` at positions `p`).

**Level 2 — Mathematical interpretation.** The theorem is a congruence/transport fact: if two state transformers (the handler executions) applied in either order land in observationally equivalent final states — which the hypotheses assert after renaming — then the same holds when the executions are packaged as the two-element event-sequence function `run_events`. It transfers, but does not *establish*, equivalence: the non-trivial content (why `sj` and `si` are observationally equivalent) must be supplied elsewhere, e.g., from heap-level commutativity plus a (currently absent) heap→observable bridge.

**Level 3 — Web/JavaScript interpretation.** In the modeled subset, *if* one has already established that firing `ev_i` on element `i` and then `ev_j` on element `j` produces the same rendered HTML and alert history as the reverse order, *then* the same holds for the `run_events` sequencing of those two dispatches. The theorem itself does **not** say which pairs of handlers are reorderable; in particular it does not follow merely from `i ≠ j` or from the handlers targeting distinct DOM elements.

### 8.4 Answers to the specific questions

- **What counts as two independent events?** Nothing is defined at event level. Independence exists only for heap operations on distinct identifiers (`i ≠ j`).
- **What may differ between them?** The theorems quantify over arbitrary `ev_i`, `ev_j`, `i`, `j` — but only the hypotheses (obs-equivalence/effect equations) make a pair reorderable.
- **Must they target different DOM elements?** No such condition appears in the event-level theorems. Distinctness (`i ≠ j`) appears only in the heap-level results.
- **Must they produce specific effects?** Only in `frame_rule_events_by_effect`, whose hypotheses require each handler's effect (on the intermediate state) to be exactly `change_element_color i ci` / `change_element_color j cj`.
- **Is `e1;e2 ≡ e2;e1` proved?** Only conditionally: given the hypotheses, yes — in the precise sense of `obs_equiv` between the two `run_events` executions. Unconditionally from structure (e.g., distinct targets): **NOT PROVED**.
- **Precise notion of equivalence:** `obs_equiv` at positions `p`: `tohtml s1 p = tohtml s2 p ∧ Alerts_s s1 = Alerts_s s2`. Not state equality, not heap-list equality, not heap-extensional equality.

### 8.5 Honest classification

`events_reorder_two` and `events_reorder_two_by_effect` are **sound but near-tautological bookkeeping theorems**: their hypotheses state, up to definitional unfolding, the observational equivalence that the conclusions assert. They are valuable as *packaging* (`run_events` interface, named intermediate states) once a real independence proof exists — but the development currently contains **no theorem** deriving the `obs_equiv` hypothesis of these results from a structural condition such as distinct targets. Consequently, the "event reordering" claimed by the proposed abstract is only partially mechanized.

---

## 9. Observational Consequences

`JSObsEquiv.thy` (with `JSAbsEvent.thy`) provides the observational layer:

**Infrastructure (PROVED):** `obs_equiv_iff_observable`; `obs_equiv_refl/sym/trans` (equivalence); `state_eq_imp_obs_equiv`; projections `obs_equiv_tohtml`, `obs_equiv_alerts`.

**Absorption → observational stability (PROVED):** `absorbed_event_preserves_obs_equiv`, `absorption_implies_obs_stable`, `absorption_implies_alerts_stable` (all conditional on `make_event_handler ev obj s = s`); concrete instances `absorbed_click_on_paragraph_obs`, `absorbed_mouseover_on_paragraph_obs`, `absorbed_mouseover_on_button_obs`, `absorbed_click_on_window_obs`, `absorbed_nonexistent_target_obs`; plus `querySelector_stable_under_absorbed_event` and `tohtml_stable_under_absorbed_event` (JSAbsEvent.thy).

**Idempotence/absorption → observational equivalence (PROVED):** `color_change_idempotent_obs` (from `change_element_color_idempotent`, JSProofs.thy), `color_change_same_result_obs`, `write_absorption_law` (from `change_element_color_absorbs`, JSFrameRule.thy).

**Connection that is MISSING (NOT PROVED):** no lemma of the form `heap_ext_eq s1 s2 ⟹ tohtml s1 p = tohtml s2 p` (nor with `Alerts_s`), and therefore no way to lift the heap-level commutativity theorems (`write_object_commute_ext` etc.) to `obs_equiv`. Verified by grep: `heap_ext_eq` occurs only in JSLocality.thy and in `frame_rule_write_object`/`frame_rule_write_dom_element`.

**Note on the equalities.** In this development: state equality (`s1 = s2`) ⇒ `obs_equiv` (proved). `heap_ext_eq` does **not** imply heap-list equality, does not imply `obs_equiv` in the mechanization, and the converse implications are likewise unproved. These distinctions must be preserved in any paper text.

---

## 10. Proof/Result Dependency Hierarchy

The real hierarchy (reconstructed) is:

```
[Foundational definitions]
  JSMemoryModel (values, expr, js_state, heap ops, browser_init_state)
  JSHTMLSyntax → JSDOM (surface syntax → heap DOM; dom_state)
  JSEval (eval_expr_fuel, run_handler)   JSHeapWF (heap_wf, freshness, preservation)
        │                                        │
[Basic semantic results]
  JSEvents (make_event_handler)                  JSLocality (load independence, heap_ext_eq,
  JSRender (tohtml)        JSProofs (idempotence,      commutativity of distinct writes)
  JSQuerySelector          last-write-wins)
  JSFuel (determinism; fuel monotonicity explicitly NOT established)
        │                                        │
[Locality results]  ← heap-extensional independence/commutativity (PROVED, cond. i≠j)
        │
[Frame rules]       ← heap-level: restatements of commutativity (PROVED, cond. i≠j)
                    ← event-level: conditional obs-equivalence transfer (PROVED, cond. on obs_equiv)
        │
[Event reordering]  ← events_reorder_two(_by_effect) (PROVED, cond. on obs_equiv of the two orders)
        │
[Observational consequences] ← obs_equiv infra; absorption→obs; idempotence→obs (PROVED)
        │
        ✗  MISSING LINK: heap_ext_eq ⟹ tohtml/obs_equiv bridge (NOT PROVED)
```

**Dependency facts (verified from the files):**
- `frame_rule_write_object` uses `write_object_commute_ext` (JSLocality); `frame_rule_write_dom_element` uses `write_dom_element_commute_ext`; `frame_rule_change_color_load` uses `load_object_change_color_independent`.
- `write_absorption_law` uses `change_element_color_absorbs` + `state_eq_imp_obs_equiv`.
- `color_change_idempotent_obs` uses `change_element_color_idempotent` (JSProofs) + `state_eq_imp_obs_equiv`.
- `absorbed_event_preserves_obs_equiv` and friends use `obs_equiv_def` + absorption facts from JSAbsEvent.
- The reordering theorems use only `run_events_two` (+ hypotheses), i.e., they sit on top of the event semantics, not on the locality results — the locality results are **not** currently connected to them.

**Conclusion:** the hypothesized chain *memory/DOM model → locality → independence → frame rule → commutativity/reordering → observational consequence* is realized **only for its heap-level prefix** (locality → independence → commutativity) and **formally disconnected** from the observational/reordering suffix. The suffix theorems are conditionally proved but not derived from the prefix.

---

## 11. Strongest Mechanized Results for the SIICUSP Paper

Recommended technical core (3–6 results):

1. **`write_object_commute_ext`** (JSLocality.thy) — distinct heap writes commute up to `heap_ext_eq`. Role: the fundamental commutativity/independence result. Scientifically important because it isolates the *entire* structural hypothesis (`i ≠ j`) and the *precise* notion of resulting equality (extensional). Connects to reordering: it is the only unconditioned commutativity available to justify swapping two effects.
2. **`write_dom_element_commute_ext`** (JSLocality.thy) — the DOM-element-level instance. Role: lifts commutativity from generic objects to DOM elements (`VDOMElement`), the building block of handler effects.
3. **`load_object_change_color_independent`** / **`frame_rule_change_color_load`** (JSLocality.thy / JSFrameRule.thy) — the footprint of a color change: changing `j` never changes what a load of `i ≠ j` observes. Role: the concrete "partes distintas do estado" statement that the abstract alludes to.
4. **`absorb_no_handler`** (JSAbsEvent.thy) + **`absorbed_event_preserves_obs_equiv`** (JSObsEquiv.thy) — events without a matching handler leave the state unchanged and preserve all observables. Role: characterizes the degenerate-but-real reorderable cases.
5. **`change_element_color_absorbs`** / **`write_absorption_law`** (JSFrameRule.thy) — repeated same-element effects collapse (last-write-wins), observationally invisible. Role: justifies ignoring repeated/disordered same-target effects.
6. **`events_reorder_two_by_effect`** (JSFrameRule.thy) — the event-sequence reordering theorem, **presented honestly as conditional**: given intermediate-state effect equations and `obs_equiv` of the two final states, the two orders of `run_events` are observationally equivalent. Role: the packaging theorem that will be the paper's principal statement **once its hypotheses are discharged** by an (essential, currently missing) independence result.

**Principal theorem candidate:** the intended principal result of the paper is the reordering theorem — `events_reorder_two_by_effect` is the closest existing candidate — but it must be presented with its conditional nature explicit, or complemented by the missing results of Section 19. As the development stands, the strongest *unconditional-in-structure* result is `write_object_commute_ext` / `write_dom_element_commute_ext`.

---

## 12. Assessment of the Proposed Research Question

> **Under which formally specified conditions can two JavaScript/DOM events or event handlers be executed in different orders without changing the observable behavior of the page?**

1. **Does the formalization contain a genuine nontrivial event-reordering result?** Partially. The reordering theorems exist and are mechanized, but their hypotheses *are* (up to unfolding) the observational equivalence of the two orders. A genuine reordering result derived from a structural independence condition (e.g., distinct targets) does **not** yet exist.
2. **Under exactly which conditions can events be reordered?** Formally: whenever the two sequential executions land in `obs_equiv` states (`events_reorder_two`), or when each handler's effect on the actual intermediate state is a color change and the two resulting states are `obs_equiv` (`events_reorder_two_by_effect`, `frame_rule_events_by_effect`). No stronger condition is mechanized.
3. **What notion of independence is actually formalized?** Extensional non-interference of heap operations on distinct identifiers: `load_object_write_independent`, `load_object_write_dom_independent`, `load_object_change_color_independent`, and commutativity `write_object_commute_ext`, `write_dom_element_commute_ext` (`heap_ext_eq`). Event/handler-level independence is **not** formalized.
4. **What notion of observable behavior is formalized?** `obs_equiv` = equality of rendered HTML (`tohtml`, at a fixed `dom_pos p`) and equality of the alert history (`Alerts_s`). Nothing else (stack, heap, event queue, selector results) is observable.
5. **What does reordering preserve?** In the proved conditional theorems: `obs_equiv` (hence `tohtml` equality and `Alerts_s` equality). Heap-level theorems preserve `heap_ext_eq` (loads), **not** the heap list, not the full state, not `tohtml` by themselves. Exact state, heap-list, and DOM-structure equality are **not** preserved or claimed.
6. **Restricted to distinct DOM elements?** The structural results are restricted to distinct **heap identifiers** (`i ≠ j`); the event-level theorems impose no distinctness and instead impose observational hypotheses.
7. **Intermediate-state assumptions?** Yes, significant: `frame_rule_events_by_effect` and `events_reorder_two_by_effect` describe effects *on the intermediate states* (the state after the first handler ran); `frame_rule_events` names the two concrete executions. The file comments acknowledge that describing handlers only on the initial state was "insufficient" and this is the corrected design.
8. **Is the frame rule conditional?** Yes — heap-level rules conditional on `i ≠ j`; event-level rules conditional on `obs_equiv`/effect hypotheses.
9. **Strongest scientifically defensible claim today:** *"In the modeled subset of JavaScript/DOM, operations on distinct heap identifiers are mutually non-interfering and commute up to extensional heap equality; events with no matching handler are absorbed, preserving the observable state (rendered HTML and alert history); repeated effects on the same element collapse to the last one; and event-sequence reordering is proved sound **conditional on** the observational equivalence of the two orders — which is currently assumed, not derived from locality."*

---

## 13. Preliminary Abstract Claim Audit

The provisional abstract (Portuguese) is audited claim by claim.

**Claim 1** — *"Aplicações web modernas são fortemente orientadas a eventos, nos quais diferentes manipuladores podem atuar sobre elementos distintos do DOM. Nesse contexto, compreender quando a ordem de execução desses eventos pode ser alterada sem modificar o comportamento observável da página é relevante…"*
- Classification: **INTERPRETATION / background** (motivation). No formal content to verify; acceptable as motivation if the rest of the abstract is accurate.

**Claim 2** — *"Este trabalho apresenta uma formalização, em Isabelle/HOL, de propriedades de independência e reordenação de eventos em um modelo simplificado de execução de JavaScript sobre o DOM."*
- Classification: **SUPPORTED (with qualification)**. A formalization in Isabelle/HOL of independence (heap-level) and reordering (conditional) exists in `Codes/`; "modelo simplificado" is accurate. Qualification: the independence mechanized is of heap operations, not of events themselves; reordering theorems are conditional.

**Claim 3** — *"A abordagem estabelece condições de localidade que permitem identificar operações que atuam sobre partes distintas do estado da página"*
- Classification: **SUPPORTED (with qualification)**. Locality = distinct heap identifiers (`i ≠ j`); "partes distintas do estado" should say "células/identificadores distintos do heap". Supporting facts: `heap_ext_eq` (JSLocality.thy), `load_object_write_independent`, etc.

**Claim 4** — *"e, a partir dessas condições, demonstrar formalmente que determinados manipuladores de eventos podem ser executados em ordens diferentes sem alterar o resultado observável"*
- Classification: **NOT CURRENTLY PROVED** — the core problem. The development contains no theorem deriving observational equivalence of reordered handler executions from the locality conditions. The locality results conclude `heap_ext_eq`; the reordering theorems **assume** `obs_equiv` of the two orders; and no bridge `heap_ext_eq ⟹ obs_equiv` exists. Files: JSLocality.thy, JSFrameRule.thy (`frame_rule_events`, `frame_rule_events_by_effect`, `events_reorder_two`, `events_reorder_two_by_effect`), JSObsEquiv.thy. Proposed corrected wording: *"a partir dessas condições, demonstra-se formalmente a comutatividade extensional das operações de escrita em células distintas do heap; a reordenação de sequências de eventos é verificada mecanicamente sob hipóteses explícitas de equivalência observacional entre as duas ordens de execução."*

**Claim 5** — *"A formalização inclui resultados de independência entre operações sobre elementos distintos"*
- Classification: **SUPPORTED (with qualification) / DIRECTLY PROVED at heap level**. Proved: `load_object_write_dom_independent`, `load_object_change_color_independent`, `write_dom_element_commute_ext` (JSLocality.thy). Qualification: "elementos distintos" must be read as distinct heap identifiers; the equality obtained is `heap_ext_eq`, not observable equivalence.

**Claim 6** — *"regras de enquadramento para eventos"* (frame rules for events)
- Classification: **NEEDS QUALIFICATION**. `frame_rule_events`/`frame_rule_events_by_effect` exist (JSFrameRule.thy) but are conditional on observational/effect hypotheses; the unconditional-structure frame rules (`frame_rule_write_object`, `frame_rule_write_dom_element`, `frame_rule_change_color_load`) are at heap level. The paper must not present them as separation-logic frame rules.

**Claim 7** — *"teoremas de comutatividade e reordenação da execução"*
- Classification: **NEEDS QUALIFICATION**. Commutativity: DIRECTLY PROVED at heap level (`write_object_commute_ext`, `write_dom_element_commute_ext`). Reordering: PROVED but conditional (`events_reorder_two`, `events_reorder_two_by_effect`). The two must be distinguished; they are currently **not** linked by any theorem.

**Claim 8** — *"As propriedades são verificadas mecanicamente pelo provador de teoremas Isabelle/HOL, fornecendo garantias formais de que os resultados decorrem das definições do modelo adotado."*
- Classification: **SUPPORTED** — the theorems are Isabelle statements with checked proofs in the `.thy` files. (Independent re-verification by Isabelle during this audit: see the Appendix and the final assessment for the executed outcome.)

**Claim 9** — *"Os resultados demonstram como técnicas de métodos formais podem ser utilizadas para caracterizar situações em que interações independentes em aplicações web preservam seu comportamento mesmo diante de diferentes ordens de execução"*
- Classification: **NOT CURRENTLY PROVED / NEEDS QUALIFICATION**. "Interações independentes … preservam seu comportamento" is precisely the claim that no current theorem establishes end-to-end: heap-level independence has not been shown to preserve `tohtml`/`Alerts_s` across reordering. Corrected wording: *"Os resultados demonstram como técnicas de métodos formais podem caracterizar, em um modelo simplificado, a comutatividade de operações sobre células distintas e a reordenação de eventos sob condições explícitas de equivalência observacional, apontando para resultados de reordenação incondicionais como trabalho futuro."*

**Special expressions check:**
- *"comportamento observável"* → legitimately refers to `obs_equiv` (JSObsEquiv.thy) = `tohtml` + `Alerts_s`. OK when used about `obs_equiv`-theorems.
- *"manipuladores podem ser executados em ordens diferentes"* → only supported **conditionally** (Claim 4).
- *"operações sobre partes distintas do estado"* → must be "operações sobre identificadores distintos do heap" (`i ≠ j`).
- *"independência entre operações sobre elementos distintos"* → heap-level only (Claim 5).
- *"regras de enquadramento para eventos"* → conditional frame rules (Claim 6).
- *"comutatividade"* → `heap_ext_eq`-commutativity at heap level; **not** `obs_equiv`-commutativity of handlers.
- *"reordenação da execução"* → `run_events` reordering, conditional (Claim 7).
- *"preservam seu comportamento"* → **not** currently proved from independence; only absorption and same-element collapse preserve observables unconditionally.

---

## 14. Assessment of the Proposed Title

**Title:** *Formal Verification of Event Independence and Reordering in JavaScript with Isabelle/HOL* (PT: *Verificação Formal de Independência e Reordenação de Eventos em JavaScript com Isabelle/HOL*).

**Classification: TOO BROAD** (for the current mechanization).

Reasoning: the title asserts formal verification of **event independence**, but event/handler-level independence is not defined or proved anywhere; only heap-operation independence on distinct identifiers is. It also asserts **event reordering**, which exists but only as conditional theorems whose hypotheses contain the observational equivalence being concluded. The title accurately describes the *research program* but overstates the *current results*. (If the essential results of Section 19 are mechanized, the title becomes defensible as written, modulo "JavaScript" → "a simplified JavaScript/DOM model".)

Alternative, more precise titles:

1. EN: *Locality, Commutativity, and Conditional Event Reordering in a Mechanized JavaScript/DOM Model* — PT: *Localidade, Comutatividade e Reordenação Condicional de Eventos em um Modelo Mecanizado de JavaScript/DOM*
2. EN: *Formalizing Heap Locality and Event Reordering in a Simplified JavaScript DOM Semantics with Isabelle/HOL* — PT: *Formalização de Localidade de Heap e Reordenação de Eventos em uma Semântica Simplificada de DOM em JavaScript com Isabelle/HOL*
3. EN: *Independence of Distinct Heap Cells and Event Reordering in a Verified JavaScript/DOM Subset* — PT: *Independência de Células Distintas do Heap e Reordenação de Eventos em um Subconjunto Verificado de JavaScript/DOM*

---

## 15. Relationship to the Previous Observational-Equivalence Work

Based on the artifacts present in this workspace (the previous project's files are not present; the comparison uses the infrastructure visible here, which the prompt states originates from the earlier observational-equivalence research).

### Reused infrastructure
- The memory/value/expression model (`js_vle`, `expr`, `js_state`, heap operations) — JSMemoryModel.thy.
- The DOM construction from surface HTML (`dom_state`) — JSHTMLSyntax.thy, JSDOM.thy.
- The evaluator and handler execution (`eval_expr_fuel`, `run_handler`) — JSEval.thy.
- The event dispatch (`make_event_handler`) — JSEvents.thy.
- The renderer `tohtml` and `dom_pos` — JSRender.thy.
- The observational definitions `observable`/`obs_equiv` — JSObsEquiv.thy.
- The absorption theory — JSAbsEvent.thy; idempotence basics — JSProofs.thy; well-formedness — JSHeapWF.thy; fuel/determinism — JSFuel.thy; selectors — JSQuerySelector.thy.

### New central focus
- **Locality and independence:** `heap_ext_eq`, the `load_object_*_independent` family, and the commutativity theorems (JSLocality.thy).
- **Frame rules and event reordering:** `run_events`, `frame_rule_*`, `events_reorder_*` (JSFrameRule.thy).

### Overlap
- Observational equivalence is unavoidable overlap: `obs_equiv` is the *observable* used by the reordering conclusions, and `tohtml` is the rendering backbone.
- Absorption results serve both narratives (they are the trivial reorderable cases).

### Distinction
- The previous question was *equivalence*: when are two programs/states observably equal? The new question is *reordering*: when can the **order of execution of event dispatches** be swapped without changing the observable, and what **locality/frame conditions** justify the swap? The technical objects that are new are the commutativity theorems, the frame rules, and the `run_events` reordering statements.
- **Honest assessment:** the distinction is real at the level of research question and of the heap-level results, but the current mechanization has **not yet delivered** the flagship event-level reordering theorem, so the scientific distance from the previous work is currently smaller than the proposal implies. The paper will be genuinely distinct only if the essential missing results (Section 19) are added, or if the paper is reframed around heap locality/commutativity with conditional reordering presented as its consequence-by-assumption.

---

## 16. Limitations and Claims We Must Not Make

Verified limitations of **this** development (each confirmed against the files):

1. **Simplified JavaScript semantics (confirmed).** The expression language has 8 constructors; `eval_binop` supports only `+` on numbers (anything else → `VTypeError`); no loops, objects literals, arrays, exceptions, prototypes, `var` scoping subtleties, or full ECMAScript. Any claim must say "subset/simplified model".
2. **Simplified DOM (confirmed).** DOM elements are flat property lists in the heap (`VDOMElement tag props`); the renderer flattens them by a position map (`dom_pos`); there is no tree mutation API in handlers, no attribute-get/set generality beyond `color`, no CSS or layout.
3. **Restricted event semantics (confirmed).** Only `EvClick`/`EvMouseOver`; handlers looked up directly on the target element property; no bubbling/capture, no propagation control, no event object, no `preventDefault`. The declared `event`/`event_queue`/`Events_s` field is **dead code**: `Events_s` is never read/written by the event or evaluation machinery (grep-verified).
4. **No real-browser concurrency / no event loop (confirmed).** Dispatch is a synchronous, deterministic state transformer (`make_event_handler`); there is no task/microtask queue, no promises, no asynchrony. Claiming relevance to real browser event-loop behavior is unsupported.
5. **Restricted handler effects (confirmed).** Modeled effects are: `alert` (append to `Alerts_s`), `changeColor` (single-element color write), `createElement` (allocation). No handler in the development removes nodes, reorders the DOM, or writes arbitrary properties.
6. **Distinct-identifier assumptions (confirmed).** All independence/commutativity theorems require `i ≠ j`; there is no aliasing/reachability analysis.
7. **Intermediate-state assumptions (confirmed).** `frame_rule_events`, `frame_rule_events_by_effect`, `events_reorder_two`, `events_reorder_two_by_effect` all carry hypotheses about the actual intermediate/final states or their `obs_equiv`.
8. **heap equality vs observational equivalence (confirmed).** `heap_ext_eq` (all loads agree) is **not** connected to `tohtml`/`obs_equiv`; state equality ⇒ `obs_equiv` is proved, the converse and the heap bridges are not. The paper must not conflate these.
9. **Rendering model limits (confirmed).** `tohtml` depends on the heap list and a fixed `dom_pos`; no lemma shows order/permutation robustness, and `obs_equiv` is parameterized by `p`.
10. **No fuel monotonicity (confirmed).** JSFuel.thy explicitly documents that `eval_expr_fuel n … = (v,s') ∧ ¬out_of_fuel v ∧ n ≤ m ⟹ eval_expr_fuel m … = (v,s')` is **not** established, and that fuel exhaustion does not propagate through compound expressions (e.g., `eval_binop` can overwrite the out-of-fuel error). `default_fuel = 200` is an arbitrary bound; claims about "the semantics" should acknowledge fuel.
11. **No browser-engine validation (confirmed).** Nothing links the model to any real engine or the HTML spec's event loop.
12. **No full ECMAScript semantics (confirmed).** See 1.

Consequences for the paper: every strong claim must be scoped to "the modeled subset"; the paper must not claim real-browser guarantees; it must not equate heap-extensional equality with observational equivalence; and it must present the reordering theorems with their hypotheses.

---

## 17. Recommended SIICUSP Paper Structure

(Based on the edital's Anexo I: abstract of up to 2 pages, two-column, sections below; submitted in Portuguese **and** English.)

1. **Título (PT/EN per file)** — use a qualified title per Section 14.
2. **Objetivos** — pose the research question exactly as in Section 12; state the hypotheses to be checked (locality ⇒ independence ⇒ reordering ⇒ observables). Isabelle theories: the whole development (overview). Present: the question, not results.
3. **Métodos e Procedimentos** — model summary: `js_state`, heap, `VDOMElement`, `eval_expr_fuel`/`run_handler`, `make_event_handler`, `tohtml`, `observable`/`obs_equiv`, `heap_ext_eq`, `run_events`; Isabelle/HOL + checked proofs; theory map (JSMemoryModel → … → JSFrameRule). Present: one small figure of the dependency map; equations numbered per edital rules. Omit: `value` demos, selector details, fuel internals (one line).
4. **Resultados** — the 3–6 results of Section 11, stated with exact names and hypotheses; distinguish `heap_ext_eq` from `obs_equiv` explicitly; state the reordering theorems **with their assumptions**. Present: `write_object_commute_ext`, `write_dom_element_commute_ext`, `load_object_change_color_independent`, `absorb_no_handler`+`absorbed_event_preserves_obs_equiv`, `change_element_color_absorbs`/`write_absorption_law`, `events_reorder_two_by_effect` (conditional). Omit: well-formedness lemma cascade (cite as invariant), selector wrappers.
5. **Conclusões** — answer the research question with qualification (what is proved: heap locality/commutativity, absorption, conditional reordering; what is open: the heap→observable bridge and handler independence). Mention limitations (Section 16) and the planned next proofs. End with the required declarations: conflict of interest; author contributions; scholarship (if any).
6. **Referências bibliográficas** — Isabelle/HOL (Nipkow, Paulson, Wenzel); separation logic (Reynolds) only if the frame-rule discussion warrants it (note the model is **not** separation logic); HTML/DOM event model reference; previous project reference; maybe a JavaScript semantics survey reference. Keep to a handful — 2 pages total.

The article must remain centered on **independence and reordering**, using the evaluator/DOM/renderer only as infrastructure.

---

## 18. SIICUSP Template/Edital Requirements

Extracted from `Siicusp/edital.pdf` (34th SIICUSP) and `Siicusp/template.doc` / `template (1).doc` (two nearly identical 2-page Word templates, ~830–850 words of placeholder text):

- **Document:** "Resumo" (abstract), **up to 2 pages**, with the 34th SIICUSP logo, organized in: (a) Título; (b) Autor(es), colaborador(es) e orientador; (c) Unidade e Universidade; (d) E-mail do primeiro autor; (e) Objetivos; (f) Métodos e Procedimentos; (g) Resultados; (h) Conclusões (parciais ou finais); (i) Declaração de conflito de interesses; (j) Contribuições de cada autor (if more than one); (k) informação sobre bolsa acadêmica (if any); (l) Referências Bibliográficas.
- **Language:** written in Portuguese **and** English (two PDF files; foreign students may submit only English).
- **Formatting:** A4 (210×297 mm); margins top 3.3 cm, bottom 4.2 cm, left/right 2.6 cm (mirror margins); two columns of 7.5 cm each with 0.8 cm spacing; Arial; titles/subtitles 13 pt bold centered; names 13 pt bold centered; faculty/university 13 pt centered; e-mail 10 pt centered; body text justified, single spacing, 10 pt.
- **Equations:** on separate lines, numbered. **Tables:** numbered, captions above (9 pt, no bold/italic), may span both columns. **Figures:** numbered, captions below (9 pt), may span both columns.
- **Template header:** TÍTULO; Autor(es) – Estudante(s) de Graduação; Colaborador(es) (máximo 3); Orientador(a); Faculdade/Universidade; E-mail do primeiro autor.
- **Submission constraints:** registration 20/07–24/08/2026; two PDFs (PT and EN abstract); title identical in form, abstract, and presentation; abstracts out of the template will not be published; corrected abstracts until 26/10/2026; 1st stage presentations 01/09–19/10/2026; international stage 25–26/11/2026 (materials in English).
- **Evaluation criteria (Anexo II):** content knowledge, methodology virtues/limitations, results understanding, conclusions answering the research question, relevance; oral clarity; abstract synthetic, adequate references, compliant with the template.
- **Note on `Siicusp/document.pdf`:** a 1-page digitally signed document from the São Paulo State Public Security Secretariat (police civil ID) — **unrelated to SIICUSP formatting**; it is not part of the edital/template material. It was extracted textually and contains no SIICUSP instructions. `template.doc`/`template (1).doc` were inspected via `textutil` conversion (no original modified).

---

## 19. Open Questions or Missing Proofs

Current state: the formalization is **internally coherent** and sufficient for a paper centered on *heap locality, commutativity, absorption, and conditional reordering*. It is **not yet sufficient** for the strong claim of the proposed abstract/title. Missing mechanized results, classified:

1. **Heap→observable bridge** — `heap_ext_eq s1 s2 ⟹ tohtml s1 p = tohtml s2 p` (plus an `Alerts_s`-preservation condition or an alert-free hypothesis). Currently missing; needed to lift `write_object_commute_ext`/`write_dom_element_commute_ext` to `obs_equiv`. Theories involved: JSLocality.thy, JSRender.thy, JSObsEquiv.thy. Classification: **ESSENTIAL**.
2. **Handler-footprint / independence lemma** — e.g., if a handler's body only `changeColor`s its own target and emits no alerts, then `make_event_handler` preserves loads of other ids (or some precise effect characterization sufficient for reordering). Currently missing; the reordering theorems' effect hypotheses (`HI`/`HJ`) are never discharged. Theories: JSEval.thy, JSEvents.thy, JSLocality.thy, JSFrameRule.thy. Classification: **ESSENTIAL**.
3. **Unconditional reordering theorem** — the flagship result: two handlers targeting distinct elements, with color-change-only effects and no alerts, can be reordered preserving `obs_equiv` (ideally stated via `run_events`). Follows once (1)+(2) exist. Classification: **ESSENTIAL** (for the paper as proposed).
4. **`tohtml` congruence under heap permutation / order robustness** — `collect_dom_nodes`/`sort_by_pos` currently has no correctness lemmas; a permutation-invariance lemma would make (1) robust and is independently valuable. Theories: JSRender.thy. Classification: **STRONGLY RECOMMENDED**.
5. **Concrete reordered instance** — a proved instance on a state with two handler-bearing distinct elements (the current `dom_state` has only one click handler; `sample_html` would need a second handler-bearing element), e.g., `obs_equiv (run_events [(EvClick,2),(EvMouseOver,3)] s) (run_events [(EvMouseOver,3),(EvClick,2)] s) sample_pos`. Classification: **STRONGLY RECOMMENDED** (paper illustration).
6. **`obs_equiv` congruence (context lemma)** — `obs_equiv s1 s2 p ∧ … ⟹ obs_equiv (run_events l s1) (run_events l s2) p` (determinism + congruence of dispatch) would let reordering compose with further events. Theories: JSObsEquiv.thy, JSFrameRule.thy, JSFuel.thy. Classification: **STRONGLY RECOMMENDED**.
7. **n-ary reordering / permutation of event sequences** — beyond two events, via fold-permutation results. Classification: **OPTIONAL**.
8. **Fuel monotonicity for the evaluator** — JSFuel.thy itself flags this as unproved; relevant only if the paper discusses semantics adequacy. Classification: **OPTIONAL** (unless fuel is discussed).
9. **Event-queue semantics** — making `Events_s` live (pending events, dispatch loop) would widen the "reordering" story to queue reordering. Classification: **OPTIONAL**.

Per instructions, none of these were implemented during this audit.

---

## 20. Final Assessment

- **Completeness:** all 14 `.thy` files were read in full (2,822 lines total); every theorem/lemma (102 declarations) was inventoried with its file and line.
- **Verified claims:** the three named results **exist and are proved**: `frame_rule_events` (JSFrameRule.thy:110), `events_reorder_two` (JSFrameRule.thy:177), `events_reorder_two_by_effect` (JSFrameRule.thy:198) — all **conditional** on observational hypotheses; `frame_rule_events_by_effect` (JSFrameRule.thy:139) likewise.
- **Isabelle verification:** an independent verification of the copied theories was executed with Isabelle2025-2 and **completed successfully** — `isabelle process_theories` processed all 14 theories with exit code 0, zero error lines, and only benign "duplicate rewrite rule" warnings (exact commands and outcomes in the Appendix); no theory file in `Codes/` was modified.
- **Proposed abstract:** requires revision — specifically Claim 4 ("…demonstrar formalmente que determinados manipuladores… podem ser executados em ordens diferentes sem alterar o resultado observável") is **NOT CURRENTLY PROVED**; Claims 3, 5, 6, 7, 9 need qualification.
- **Proposed title:** **TOO BROAD** for the current mechanization (alternatives in Section 14).
- **Sufficiency for the SIICUSP paper:** sufficient for an honest paper on heap locality/commutativity/absorption with *conditional* reordering; **not sufficient** for the paper as the provisional abstract describes it. The gap can be closed by the ESSENTIAL results of Section 19 (heap→observable bridge, handler-footprint lemma, unconditional reordering theorem) — mechanically plausible within the existing theories.
- **Most important limitation:** the missing link between extensional heap equality (`heap_ext_eq`) and observational equivalence (`obs_equiv`), which leaves the event-reordering theorems with observational-equivalence assumptions that nothing in the development discharges from structural conditions.
- **Strongest scientifically defensible claim:** as stated in Section 12, item 9.

---

## Appendix — Isabelle verification (Section 19 of the task)

- **Availability:** `/opt/homebrew/bin/isabelle` → `Isabelle2025-2` (also `/Applications/Isabelle2025.app`, `/Applications/Isabelle2025-2.app`). Isabelle/HOL was executed during this audit.
- **Non-destructive procedure:** the 14 `.thy` files were **copied** to `/tmp/isaudit/AuditSession/` (no file under the workspace was modified); a minimal `ROOT` file (`session AuditSession = HOL + options [document = false] theories [JSFrameRule]`) was created **in /tmp only**.
- **Attempt 1 (session build):** `isabelle build -d /tmp/isaudit -b AuditSession` → failed with `*** Bad session root directory: "/private/tmp/isaudit" (missing "ROOT" or "ROOTS")` — a path error (the ROOT file is in the session subdirectory), not a theory error.
- **Attempt 2 (session build, corrected path):** `isabelle build -d /tmp/isaudit/AuditSession -b AuditSession` → failed with `*** [SQLITE_CANTOPEN] Unable to open the database file`. Retried with `-o build_database=false`, and with `ISABELLE_HOME_USER`/`ISABELLE_OUTPUT`/`ISABELLE_BROWSER_INFO` pointed at freshly created writable directories under `/tmp` — same error. Root cause identified: the execution environment denies writes to `~/.isabelle/Isabelle2025-2` (`touch` → `Operation not permitted`), and `isabelle build` needs its SQLite host database there; the environment override of `ISABELLE_HOME_USER` is ignored by the Isabelle2025-2 launcher. This is an **environment limitation**, not a theory error. No repair of any theory was attempted.
- **Successful verification (ad-hoc theory processing, no session database):** `isabelle process_theories -l HOL -D /tmp/isaudit/AuditSession -O -v JSMemoryModel JSHTMLSyntax JSDOM JSEval JSEvents JSRender JSQuerySelector JSHeapWF JSLocality JSProofs JSFuel JSAbsEvent JSObsEquiv JSFrameRule`
  - **Outcome:** exit code **0** (success); log ends with `Timing Draft (8 threads, 101.872s elapsed time, …)` and `Finished Draft (0:01:43 elapsed time, …)`.
  - All **14** theories were processed (`Draft: theory Draft.JSMemoryModel` … `Draft.JSFrameRule`); **0** lines matching `***` (no errors); the only warnings are benign `Ignoring duplicate rewrite rule` notices (from `simp add: …simps`), plus normal `Output` lines from the theories' `value` commands.
- **Conclusion:** the 14 theories of `Codes/` **were independently verified by Isabelle/HOL (Isabelle2025-2) during this audit**, on byte-identical copies, without any modification. This audit therefore does **not** fall under the "statically audited but not independently verified" disclaimer.
