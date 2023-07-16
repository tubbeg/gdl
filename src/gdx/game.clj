(ns gdx.game
  (:require [gdx.utils :refer (set-var-root)]
            [gdx.app :as app]
            [gdx.graphics :as g])
  (:import [com.badlogic.gdx.utils ScreenUtils]
           [com.badlogic.gdx Screen Game]))

(defmacro defscreen [var-name & screen]
  `(def ~var-name (hash-map ~@screen)))

(defn- screen->libgdx-screen [{:keys [show render update dispose]}]
  (reify Screen
    (show [_]
      (when show
        (show)))
    (render [_ delta]
      (ScreenUtils/clear g/black)
      (g/fix-viewport-update)
      (when render
        (render))
      (when update
        (update (* delta 1000))))
    (resize [_ w h])
    (pause [_])
    (resume [_])
    (hide [_])
    (dispose [_]
      (when dispose
        (dispose)))))

(declare ^:private screens)

(defn set-screen [k]
  (.setScreen ^Game (.getApplicationListener app/app)
              (k screens)))

(defn create [screens]
  (let [screens (zipmap
                 (keys screens)
                 (map screen->libgdx-screen (vals screens)))
        game (proxy [Game] []
               (create []
                 (app/call-on-create-fns!)
                 (set-screen (first (keys screens))))
               (dispose []
                 (app/call-on-destroy-fns!)
                 (doseq [screen (vals screens)]
                   (.dispose ^Screen screen)))
               (pause [])
               (resize [w h]
                 (g/on-resize w h))
               (resume []))]
    (set-var-root #'screens screens)
    game))
