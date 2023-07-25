(ns gdl.ecs
  (:require [gdl.session :as session]))

(defmacro defsystem
  "A system is a multimethod which dispatches on an attribute."
  [symbol args]
  `(defmulti ~symbol (fn [~'a ~@args] ~'a)))

(defmacro extend-system [system a f]
  `(defmethod ~system ~a ~(symbol (str (name system) "." (name a)))
     [& [~'_ & ~'args]]
     (apply ~f ~'args)))

(defmacro extend-systems [a & system-fns]
  `(do
    ~@(for [[system & fn-body] system-fns]
        (list `extend-system system a `(fn ~@fn-body)))
    ~a))

(defn apply-system! [system entity]
  (let [entity* @entity]
    (doseq [[a f] (methods system)
            :when (contains? entity* a)]
      (f a entity))))

(def ^:private ids->entities (atom nil))

(session/defstate state
  (load!  [_ data]
   (reset! ids->entities {}))
  (serialize [_])
  (initial-data [_]))

(defn get-entity [id]
  (get @ids->entities id))

(defn exists? [entity]
  (get-entity (:id @entity)))

(defsystem on-create-entity    [entity])
(defsystem after-create-entity [entity])
(defsystem on-destroy-entity   [entity])

(extend-systems :id
  (on-create-entity [entity]
    (swap! ids->entities assoc (:id @entity) entity))
  (on-destroy-entity [entity]
    (swap! ids->entities dissoc (:id @entity))))

(let [cnt (atom 0)]
  (defn- unique-number! []
    (swap! cnt inc)))

(defn create-entity! [properties]
  {:pre [(not (contains? properties :id))]}
  (let [entity (atom (assoc properties :id (unique-number!)))]
    (apply-system! on-create-entity    entity)
    (apply-system! after-create-entity entity)
    entity))

(extend-systems :parent
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

; first destroy entity, then not necessary for children to remove themself anymore @ parent :children
(defn destroy-to-be-removed-entities! []
  (doseq [entity (filter (comp :destroyed? deref) (vals @ids->entities))
          entity (if-let [children (:children @entity)]
                   (cons entity children)
                   [entity])
          :when (exists? entity)]
    (apply-system! on-destroy-entity entity)))

;;
;;
;; Update system (separate file/ns ?)
;;
;;

; # Why do we use a :blocks counter and not a boolean?
; Different effects can stun/block for example :movement component
; and if we remove the effect, other effects still need to be there
; so each effect increases the :blocks-count by 1 and decreases them after the effect ends.

(defn- blocked? [component]
  (when-let [blocks-count (:blocks component)]
    (assert (and (integer? blocks-count)
                 (>= blocks-count 0)))
    (> blocks-count 0)))

(defn- update-speed [component]
  (or (:update-speed component) 1))

(defsystem update-component [v       delta])
(defsystem update-entity*   [entity* delta])
(defsystem update-entity!   [entity  delta])

(def ^:private system-apply-fns
  {#'update-component (fn [f a entity delta] (swap! entity update a #(f a % delta)))
   #'update-entity*   (fn [f a entity delta] (swap! entity #(f a % delta)))
   #'update-entity!   (fn [f a entity delta] (f a entity delta))})

(defn- update-entity!* [entity delta]
  (doseq [[system-var apply-fn] system-apply-fns
          [a f] (methods @system-var)
          :let [component (a @entity)] ; TODO if has implementation, not if key not falsey ... later ...
          :when component
          :let [delta (->> (update-speed component) (* delta) int (max 0))]
          ; TODO what if speed =0 ??
          :when (not (blocked? component))]
    (try
     (apply-fn f a entity delta)
     (catch Throwable t
       (println "Entity id " (:id @entity) " attribute: " a " system: " (:name (meta system-var)))
       (throw t)))))

(defn update-entities! [entities delta]
  (doseq [entity entities]
    (update-entity!* entity delta)))
