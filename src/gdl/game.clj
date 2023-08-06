(ns gdl.game
  (:require [gdl.utils :refer :all]
            [gdl.app :as app]
            [gdl.assets :as assets]
            gdl.files
            [gdl.graphics :as g]
            [gdl.graphics.color :as color]
            gdl.input)
  (:import [com.badlogic.gdx.utils ScreenUtils]
           [com.badlogic.gdx Gdx Screen ScreenAdapter Game]))

(defn- load-gdx-globals []
  (set-var-root #'gdl.app/app           Gdx/app)
  (set-var-root #'gdl.files/files       Gdx/files)
  (set-var-root #'gdl.graphics/graphics Gdx/graphics)
  (set-var-root #'gdl.input/input       Gdx/input))

(defn- load-assets []
  (set-var-root #'assets/manager (assets/asset-manager))
  (set-var-root #'assets/sounds-folder "sounds/")
  (assets/load-all {:folder "resources/" ; TODO these are classpath settings ?
                    :sound-files-extensions #{"wav"}
                    :image-files-extensions #{"png" "bmp"}}))

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
  (.setScreen ^Game (.getApplicationListener app/app) (k screens)))

; TODO game main config !
(def graphics-config {:gui-unit-scale 1
                      :world-unit-scale 48})

; screens are map of keyword to screen
; for handling cyclic dependencies
; (options screen can set main screen and vice versa)
(defn create [screens] ; TODO keys->screens / or key->screen ?? / hashmap naming ?
  (let [screens (zipmap
                 (keys screens)
                 (map screen->libgdx-screen (vals screens)))
        game (proxy [Game] []
               (create []
                 (load-gdx-globals)
                 (load-assets)

                 (g/load-state graphics-config)
                 (fire-event! :app/create)
                 (set-screen (first (keys screens))))
               (dispose []
                 (fire-event! :app/destroy)
                 ; this is not disposable interface, screen has separate dispose method
                 (doseq [screen (vals screens)]
                   (.dispose ^Screen screen))
                 (g/dispose-state)
                 (dispose assets/manager))
               (pause [])
               (resize [w h]
                 (g/on-resize w h))
               (resume []))]
    (set-var-root #'screens screens)
    game))
