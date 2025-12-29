(ns validate-graph.validators
  "Semantic validators for proof graphs beyond schema validation.
   Checks referential integrity, acyclicity, scope validity, and taint correctness."
  (:require [clojure.set :as set]))

;; =============================================================================
;; Referential Integrity
;; =============================================================================

(defn check-dependency-refs
  "Check that all :dependencies reference existing nodes."
  [graph]
  (let [node-ids (set (keys (:nodes graph)))
        errors (for [[node-id node] (:nodes graph)
                     dep-id (:dependencies node)
                     :when (not (contains? node-ids dep-id))]
                 {:type :missing-dependency
                  :node-id node-id
                  :missing-ref dep-id
                  :message (str "Node " node-id " depends on non-existent node " dep-id)})]
    (vec errors)))

(defn check-parent-refs
  "Check that all :parent references point to existing nodes."
  [graph]
  (let [node-ids (set (keys (:nodes graph)))
        errors (for [[node-id node] (:nodes graph)
                     :let [parent (:parent node)]
                     :when (and parent (not (contains? node-ids parent)))]
                 {:type :missing-parent
                  :node-id node-id
                  :missing-ref parent
                  :message (str "Node " node-id " has non-existent parent " parent)})]
    (vec errors)))

(defn check-lemma-refs
  "Check that :lemma-ref nodes reference existing lemmas."
  [graph]
  (let [lemma-ids (set (keys (:lemmas graph)))
        errors (for [[node-id node] (:nodes graph)
                     :when (= :lemma-ref (:type node))
                     :let [lemma-id (:lemma-id node)]
                     :when (not (contains? lemma-ids lemma-id))]
                 {:type :missing-lemma
                  :node-id node-id
                  :missing-ref lemma-id
                  :message (str "Node " node-id " references non-existent lemma " lemma-id)})]
    (vec errors)))

(defn check-external-refs
  "Check that :external-ref nodes reference existing external-refs."
  [graph]
  (let [ext-ids (set (keys (:external-refs graph)))
        errors (for [[node-id node] (:nodes graph)
                     :when (= :external-ref (:type node))
                     :let [ext-id (:external-id node)]
                     :when (not (contains? ext-ids ext-id))]
                 {:type :missing-external-ref
                  :node-id node-id
                  :missing-ref ext-id
                  :message (str "Node " node-id " references non-existent external-ref " ext-id)})]
    (vec errors)))

(defn check-symbol-refs
  "Check that symbol :introduced-at references existing nodes."
  [graph]
  (let [node-ids (set (keys (:nodes graph)))
        errors (for [[sym-id sym] (:symbols graph)
                     :let [intro-at (:introduced-at sym)]
                     :when (not (contains? node-ids intro-at))]
                 {:type :missing-symbol-intro
                  :symbol-id sym-id
                  :missing-ref intro-at
                  :message (str "Symbol " sym-id " introduced at non-existent node " intro-at)})]
    (vec errors)))

(defn check-lemma-root-refs
  "Check that lemma :root-node references exist in archived-nodes."
  [graph]
  (let [archived-ids (set (keys (:archived-nodes graph)))
        node-ids (set (keys (:nodes graph)))
        all-ids (set/union archived-ids node-ids)
        errors (for [[lemma-id lemma] (:lemmas graph)
                     :let [root (:root-node lemma)]
                     :when (not (contains? all-ids root))]
                 {:type :missing-lemma-root
                  :lemma-id lemma-id
                  :missing-ref root
                  :message (str "Lemma " lemma-id " has non-existent root-node " root)})]
    (vec errors)))

(defn check-referential-integrity
  "Run all referential integrity checks."
  [graph]
  (concat
   (check-dependency-refs graph)
   (check-parent-refs graph)
   (check-lemma-refs graph)
   (check-external-refs graph)
   (check-symbol-refs graph)
   (check-lemma-root-refs graph)))

;; =============================================================================
;; Acyclicity
;; =============================================================================

(defn find-cycle
  "Find a cycle in the dependency graph using DFS with coloring.
   Returns nil if no cycle, or a vector of node IDs forming the cycle."
  [graph]
  (let [nodes (:nodes graph)]
    (when (seq nodes)
      (let [;; WHITE = 0, GRAY = 1, BLACK = 2
            color (atom (zipmap (keys nodes) (repeat 0)))
            parent (atom {})
            cycle-found (atom nil)]
        (doseq [start (keys nodes)
                :while (nil? @cycle-found)]
          (when (zero? (get @color start 2))
            ;; DFS from this node
            (loop [stack [start]]
              (when (and (seq stack) (nil? @cycle-found))
                (let [node (peek stack)]
                  (case (get @color node 2)
                    ;; WHITE - not visited, start processing
                    0 (do
                        (swap! color assoc node 1)  ; Mark GRAY
                        (let [deps (get-in nodes [node :dependencies] #{})
                              valid-deps (filter #(contains? nodes %) deps)]
                          (if (empty? valid-deps)
                            ;; No deps, mark BLACK and pop
                            (do
                              (swap! color assoc node 2)
                              (recur (pop stack)))
                            ;; Check deps
                            (let [gray-dep (first (filter #(= 1 (get @color % 2)) valid-deps))]
                              (if gray-dep
                                ;; Found back edge = cycle!
                                (let [;; Reconstruct cycle from parent chain
                                      cycle-path (loop [path [gray-dep]
                                                        curr node]
                                                   (if (= curr gray-dep)
                                                     path
                                                     (recur (conj path curr)
                                                            (get @parent curr))))]
                                  (reset! cycle-found (vec (reverse cycle-path))))
                                ;; Push unvisited deps
                                (let [white-deps (filter #(zero? (get @color % 2)) valid-deps)]
                                  (doseq [d white-deps]
                                    (swap! parent assoc d node))
                                  (if (empty? white-deps)
                                    (do
                                      (swap! color assoc node 2)
                                      (recur (pop stack)))
                                    (recur (into stack white-deps)))))))))
                    ;; GRAY - currently processing, should be handled above
                    1 (do
                        ;; All deps processed, mark BLACK
                        (swap! color assoc node 2)
                        (recur (pop stack)))
                    ;; BLACK - already done
                    2 (recur (pop stack))))))))
        @cycle-found))))

(defn check-acyclicity
  "Check that the dependency graph has no cycles."
  [graph]
  (if-let [cycle (find-cycle graph)]
    [{:type :dependency-cycle
      :cycle cycle
      :message (str "Dependency cycle detected: " (clojure.string/join " -> " cycle))}]
    []))

;; =============================================================================
;; Scope Validation
;; =============================================================================

(defn get-ancestors
  "Get all transitive dependencies of a node (ancestors in the DAG)."
  [graph node-id]
  (let [nodes (:nodes graph)]
    (loop [stack [node-id]
           visited #{}]
      (if (empty? stack)
        (disj visited node-id)
        (let [current (peek stack)
              stack (pop stack)]
          (if (contains? visited current)
            (recur stack visited)
            (let [deps (get-in nodes [current :dependencies] #{})]
              (recur (into stack deps) (conj visited current)))))))))

(defn compute-valid-scope
  "Compute which local-assume nodes are validly in scope for a node."
  [graph node-id]
  (let [nodes (:nodes graph)
        ancestors (get-ancestors graph node-id)
        ;; Find local-assume nodes among ancestors
        assumes (->> ancestors
                     (filter #(= :local-assume (get-in nodes [% :type])))
                     set)
        ;; Find discharged assumptions among ancestors
        discharged (->> ancestors
                        (filter #(= :local-discharge (get-in nodes [% :type])))
                        (map #(get-in nodes [% :discharges]))
                        set)]
    (set/difference assumes discharged)))

(defn check-scope-validity
  "Check that all nodes have valid :scope entries."
  [graph]
  (let [errors (for [[node-id node] (:nodes graph)
                     :let [actual-scope (:scope node)
                           valid-scope (compute-valid-scope graph node-id)
                           invalid-entries (set/difference actual-scope valid-scope)]
                     :when (seq invalid-entries)]
                 {:type :invalid-scope
                  :node-id node-id
                  :invalid-entries invalid-entries
                  :message (str "Node " node-id " has invalid scope entries: " invalid-entries)})]
    (vec errors)))

(defn check-discharge-validity
  "Check that :local-discharge nodes discharge valid in-scope ancestors."
  [graph]
  (let [nodes (:nodes graph)
        errors (for [[node-id node] nodes
                     :when (= :local-discharge (:type node))
                     :let [target (:discharges node)
                           ancestors (get-ancestors graph node-id)
                           in-scope (compute-valid-scope graph node-id)]]
                 (cond
                   (not (contains? ancestors target))
                   {:type :discharge-not-ancestor
                    :node-id node-id
                    :target target
                    :message (str "Node " node-id " discharges " target " which is not an ancestor")}

                   (not (contains? (conj in-scope target) target))
                   {:type :discharge-out-of-scope
                    :node-id node-id
                    :target target
                    :message (str "Node " node-id " discharges " target " which is not in scope")}

                   :else nil))]
    (vec (remove nil? errors))))

(defn check-scopes
  "Run all scope validation checks."
  [graph]
  (concat
   (check-scope-validity graph)
   (check-discharge-validity graph)))

;; =============================================================================
;; Taint Validation
;; =============================================================================

(defn compute-taint
  "Compute the expected taint for a node based on its status and dependencies."
  [graph node-id]
  (let [node (get-in graph [:nodes node-id])
        status (:status node)]
    (cond
      (= :admitted status) :self-admitted
      (= :rejected status) :tainted
      :else
      (let [deps (:dependencies node)
            dep-taints (map #(get-in graph [:nodes % :taint]) deps)]
        (if (some #{:tainted :self-admitted} dep-taints)
          :tainted
          :clean)))))

(defn check-taint-correctness
  "Check that all nodes have correctly computed :taint values."
  [graph]
  (let [errors (for [[node-id node] (:nodes graph)
                     :let [actual-taint (:taint node)
                           expected-taint (compute-taint graph node-id)]
                     :when (not= actual-taint expected-taint)]
                 {:type :incorrect-taint
                  :node-id node-id
                  :actual actual-taint
                  :expected expected-taint
                  :message (str "Node " node-id " has taint " actual-taint " but should be " expected-taint)})]
    (vec errors)))

;; =============================================================================
;; Combined Validation
;; =============================================================================

(defn validate-semantics
  "Run all semantic validations on a graph.
   Returns {:valid true} or {:valid false :errors [...]}."
  [graph]
  (let [errors (concat
                (check-referential-integrity graph)
                (check-acyclicity graph)
                (check-scopes graph)
                (check-taint-correctness graph))]
    (if (empty? errors)
      {:valid true}
      {:valid false :errors (vec errors)})))
