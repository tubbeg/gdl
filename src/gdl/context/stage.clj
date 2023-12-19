(ns gdl.context.stage
  (:require [gdl.context :refer [gui-mouse-position current-screen get-stage]]
            [gdl.scene2d.actor :as actor])
  (:import com.badlogic.gdx.scenes.scene2d.Stage))

(defn- find-actor-with-id [^Stage stage id]
  (let [actors (.getActors stage)
        ids (keep actor/id actors)]
    (assert (apply distinct? ids)
            (str "Actor ids are not distinct: " (vec ids)))
    (first (filter #(= id (actor/id %))
                   actors))))

(extend-type gdl.context.Context
  gdl.context/Stage
  (->stage [{:keys [gui-viewport batch]} actors]
    (let [stage (proxy [Stage clojure.lang.ILookup] [gui-viewport batch]
                  (valAt
                    ([id]
                     (find-actor-with-id this id))
                    ([id not-found]
                     (or (find-actor-with-id this id)
                         not-found))))]
      (doseq [actor actors]
        (.addActor stage actor))
      stage))
  (get-stage [context]
    (:stage (current-screen context)))
  (mouse-on-stage-actor? [context]
    (let [[x y] (gui-mouse-position context)]
      (.hit ^Stage (get-stage context) x y true))))
