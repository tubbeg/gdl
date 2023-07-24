(ns gdl.ecs
  (:require [gdl.session :as session]))

(def ctype-fns {})

(defmacro defctypefn [fnkey ctype & fn-body]
  `(let [ctype-fn# (fn ~(symbol (str (name fnkey) "-" (name ctype)))
                     ~@fn-body)]
    (alter-var-root #'ctype-fns assoc-in [~fnkey ~ctype] ctype-fn#)
    [~fnkey ~ctype]))

(defn call-ctype-fns! [fn-key entity]
  (let [entity* @entity]
    (doseq [[ctype f] (get ctype-fns fn-key)
            :when (ctype entity*)]
      (f entity))))

(def ^:private ids->entities (atom nil))
(def ^:private removelist (atom nil))

(session/defstate state
  (load!  [_ data]
   (reset! ids->entities {})
   (reset! removelist #{}))
  (serialize [_])
  (initial-data [_]))

(defn get-entity [id]
  (get @ids->entities id))

(defn exists? [entity]
  (get-entity (:id @entity)))

(let [cnt (atom 0)]
  (defn- unique-number! []
    (swap! cnt inc)))

(defmacro defcomponent [kw & system-impls]
  `(do
    ~@(for [[system-name & fnbody] system-impls]
        (do
         (apply list `defctypefn (keyword (name system-name)) kw fnbody)))))

(defcomponent :id
  (on-create-entity [entity]
    (swap! ids->entities assoc (:id @entity) entity))
  (on-destroy-entity [entity]
    (swap! ids->entities dissoc (:id @entity))))

(defn create-entity! [properties]
  {:pre [(not (contains? properties :id))]}
  (let [entity (atom (assoc properties :id (unique-number!)))]
    (call-ctype-fns! :on-create-entity    entity)
    (call-ctype-fns! :after-create-entity entity)
    entity))

(defcomponent :parent
  (on-create-entity [child]
   (let [parent (:parent @child)]
     (assert (exists? parent))
     (if-let [children (:children @parent)]
       (do
        (assert (not (contains? children child)))
        (swap! parent update :children conj child))
       (swap! parent assoc :children #{child}))))
  (on-destroy-entity [child]
   (let [parent (:parent @child)]
     (when (exists? parent)
       (let [children (:children @parent)]
         (assert (contains? children child))
         (if (= children #{child})
           (swap! parent dissoc :children)
           (swap! parent update :children disj child)))))))

(defn add-to-removelist [entity]
  (swap! removelist conj entity))

; first destroy entity, then not necessary for children to remove themself anymore @ parent :children
(defn destroy-to-be-removed-entities []
  (doseq [entity @removelist
          entity (if-let [children (:children @entity)]
                   (cons entity children)
                   [entity])
          :when (exists? entity)]
    (call-ctype-fns! :on-destroy-entity entity))
  (reset! removelist #{}))
