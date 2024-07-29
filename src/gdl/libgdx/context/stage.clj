(ns ^:no-doc gdl.libgdx.context.stage
  (:require [gdl.context :refer [current-screen get-stage delta-time]]
            gdl.disposable
            [gdl.graphics :as g]
            [gdl.screen :as screen]
            [gdl.scene2d.actor :as actor]
            [gdl.scene2d.group :refer [find-actor-with-id] :as group])
  (:import com.badlogic.gdx.Gdx
           com.badlogic.gdx.scenes.scene2d.Stage))

(defrecord StageScreen [^Stage stage sub-screen]
  gdl.disposable/Disposable
  (dispose [_]
    (.dispose stage))

  gdl.screen/Screen
  (show [_ context]
    (.setInputProcessor Gdx/input stage)
    (when sub-screen (screen/show sub-screen context)))

  (hide [_ context]
    (.setInputProcessor Gdx/input nil)
    (when sub-screen (screen/hide sub-screen context)))

  (render [_ context]
    ; stage act first so user screen calls change-screen -> is the end of frame
    ; otherwise would need render-after-stage
    ; or on change-screen the stage of the current screen would still .act
    (.act stage (delta-time context))
    (when sub-screen (screen/render sub-screen context))
    (.draw stage)))

(extend-type gdl.context.Context
  gdl.context/Stage
  (->stage-screen [{{:keys [gui-viewport batch]} :gdl.libgdx.context/graphics}
                   {:keys [actors sub-screen]}]
    (let [stage (proxy [Stage clojure.lang.ILookup] [gui-viewport batch]
                  (valAt
                    ([id]
                     (find-actor-with-id (.getRoot ^Stage this) id))
                    ([id not-found]
                     (or (find-actor-with-id (.getRoot ^Stage this) id)
                         not-found))))]
      (doseq [actor actors]
        (.addActor stage actor))
      (->StageScreen stage sub-screen)))

  (get-stage [context]
    (:stage (current-screen context)))

  (mouse-on-stage-actor? [context]
    (let [[x y] (g/gui-mouse-position (:gdl.libgdx.context/graphics context))]
      (.hit ^Stage (get-stage context) x y true)))

  (add-to-stage! [ctx actor]
    (-> ctx
        get-stage
        (group/add-actor! actor))))

(extend-type Stage
  gdl.scene2d.group/Group
  (children [stage]
    (group/children (.getRoot stage)))

  (clear-children! [stage]
    (group/clear-children! (.getRoot stage)))

  (find-actor-with-id [stage id]
    (group/find-actor-with-id (.getRoot stage) id))

  (add-actor! [stage actor]
    (group/add-actor! (.getRoot stage) actor)))
