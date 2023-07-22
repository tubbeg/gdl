(ns gdx.game
  (:require [gdx.utils :refer :all]
            [gdx.app :as app]
            [gdx.graphics :as g]
            [gdx.graphics.color :as color])
  (:import [com.badlogic.gdx.utils ScreenUtils]
           [com.badlogic.gdx Screen ScreenAdapter Game]))

; ? this is defhash !?

(comment
 (defhashmap foo
   :a 1
   :b 2
   :c 3))

; is there any point to this or defcolor ?

(defmacro defscreen [var-name & screen]
  `(def ~var-name (hash-map ~@screen)))

(defn- screen->libgdx-screen [{:keys [show render update dispose]}]
  (proxy [ScreenAdapter] []
    (show []
      (when show
        (show)))
    (render [delta]
      (ScreenUtils/clear color/black)
      (g/fix-viewport-update)
      (when render
        (render))
      (when update
        (update (* delta 1000))))
    (dispose []
      (when dispose
        (dispose)))))

(declare ^:private screens)

(defn set-screen [k]
  (.setScreen ^Game (app/application-listener) (k screens)))

; screens are map of keyword to screen
; for handling cyclic dependencies
; (options screen can set main screen and vice versa)
(defn create [screens] ; TODO keys->screens / or key->screen ?? / hashmap naming ?
  (let [screens (zipmap
                 (keys screens)
                 (map screen->libgdx-screen (vals screens)))
        game (proxy [Game] []
               (create []
                 (fire-event! :app/create)
                 (set-screen (first (keys screens))))
               (dispose []
                 (fire-event! :app/destroy)
                 ; this is not disposable interface, screen has separate dispose method
                 (doseq [screen (vals screens)]
                   (.dispose ^Screen screen)))
               (pause [])
               (resize [w h]
                 (g/on-resize w h))
               (resume []))]
    (set-var-root #'screens screens)
    game))
