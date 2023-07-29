(ns gdl.ecs
  (:require [x.x :as x]
            [gdl.session :as session]))

(def ^:private ids->rs (atom nil))

(defn get-entity [id] (get @ids->rs id))
(defn exists? [r] (get-entity (:id @r)))

(session/defstate state
  (load!  [_ data]
    (reset! ids->rs {}))
  (serialize [_])
  (initial-data [_]))

(x/defsystems create-systems  [create  create! ])
(x/defsystems destroy-systems [destroy destroy!])

(let [cnt (atom 0)] ; TODO reset cnt every session ?
  (defn- unique-number! []
    (swap! cnt inc)))

(x/extend-component :id
  (create [_ _] (unique-number!)) ; TODO precondition (nil? id)
  (create!  [_ r] (swap! ids->rs assoc  (:id @r) r))
  (destroy! [_ r] (swap! ids->rs dissoc (:id @r))))

(x/defsystem after-create! [c r])

(defn create-entity! [e]
  {:pre [(not (contains? e :id))]}
  (->> (assoc e :id nil)
      atom
      (x/apply-systems! create-systems)
      (x/apply! after-create!)))

(defn destroy-to-be-removed-entities! []
  (doseq [r (filter (comp :destroyed? deref) (vals @ids->rs))
          :when (exists? r)]
    (x/apply-systems! destroy-systems r)))

; # Why do we use a :blocks counter and not a boolean?
; Different effects can stun/block for example :movement component
; and if we remove the effect, other effects still need to be there
; so each effect increases the :blocks-count by 1 and decreases them after the effect ends.
(defn- blocked? [v]
  (when-let [cnt (:blocks v)]
    (assert (and (integer? cnt)
                 (>= cnt 0))) ; TODO pos??
    (> cnt 0)))

(defn- delta-speed [delta v]
  (->> (or (:update-speed v) 1)
       (* delta)
       int
       (max 0)))

(x/defsystems tick-systems [tick tick!]
  :extra-params [delta])

(defn- tick-args [v delta]
  [(blocked? v) (delta-speed delta v)])

; TODO entity id/c/v on error print ?
(defn- tick-entity! [r delta]
  (reset! r
          (x/update-map
           (fn [c v]
             (let [[blocked? delta] (tick-args v delta)]
               (if blocked?
                 v
                 (tick c v delta))))
           @r))
  (doseq [c (keys @r)
          :let [v (c @r)
                [blocked? delta] (tick-args v delta)]
          :when (not blocked?)]
    (tick! c r delta)))

(defn tick-entities! [rs delta]
  (doseq [r rs]
    (tick-entity! r delta)))
