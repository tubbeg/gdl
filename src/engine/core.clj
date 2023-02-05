(ns engine.core
  (:require [engine.utils :refer (set-var-root)]
            [engine.asset-manager :as asset-manager]
            [engine.graphics :as g]
            [engine.input :refer (update-mousebutton-state)])
  (:import [com.badlogic.gdx.backends.lwjgl3 Lwjgl3Application Lwjgl3ApplicationConfiguration]
           [com.badlogic.gdx Gdx Screen Game]
           [com.badlogic.gdx.audio Sound])) ; TODO Sound reflection for play

(defn ^:private create-lwjgl3-application
  [& {:keys [title game width height full-screen]}]
  (let [config (Lwjgl3ApplicationConfiguration.)]
    (.setTitle config title)
    (.useVsync config true)
    (if full-screen
      (.setFullscreenMode config (Lwjgl3ApplicationConfiguration/getDisplayMode))
      (.setWindowedMode config width height))
    (println "Starting Lwjgl3Application"); TODO logging
    (Lwjgl3Application. game config)))

(defn exit-app []
  (.exit (Gdx/app)))

(defmacro with-context
  "Executes body asynchronously with graphics context"
  [& body]
  `(.postRunnable (Gdx/app)
                  (fn [] ~@body)))

(defn get-fps []
  (str (.getFramesPerSecond (Gdx/graphics))))

(defn play-sound [filestring]
  (.play (asset-manager/get-sound filestring)))

(defprotocol GameScreen
  "A game can have different screens like main-menu, player-selection, actual ingame-state, and so on.
  Graphics context is available in all functions for loading/disposing of resources."
  (show [this] "Called each time this screen is shown.")
  (destroy [this] "Called once on closing the game app")
  (render [this] "Called on every tick before update-screen")
  (update-screen [this delta] "Called on every tick with elapsed delta time in ms"))

(defn- game-screen->libgdx-screen [game-screen]
  (reify Screen
    (show [_]
      (show game-screen))
    (render [_ delta]
      (g/clear-screen)
      (g/on-update)
      (render game-screen)
      (update-mousebutton-state)
      (update-screen game-screen (* delta 1000)))
    (resize [_ w h])
    (pause [_])
    (resume [_])
    (hide [_])
    (dispose [_]
      (destroy game-screen))))

; hash of keyword -> screen
(declare ^:private screens)

(defn set-screen [k]
  (.setScreen (.getApplicationListener (Gdx/app))
              (k screens)))

(defn start-app
  "tile-size key is required if you want to use render-map / render-map-level / map-coords
  functions, otherwise not necessary."
  [& {:keys [game-screens
             full-screen
             title
             window-width
             window-height
             viewport-width
             viewport-height
             assets-folder
             on-create
             tile-size]
      :or {title "Test"
           window-width 800
           window-height 600
           viewport-width 800
           viewport-height 600
           on-create (fn [])}}]
  (let [screens (zipmap
                 (keys game-screens)
                 (map game-screen->libgdx-screen (vals game-screens)))
        game (proxy [Game] []
               (create []
                 (asset-manager/on-create assets-folder)
                 (g/initialize viewport-width viewport-height tile-size)
                 (on-create)
                 (.setScreen this (first (vals screens))))
               (dispose []
                 (asset-manager/on-dispose)
                 (g/on-dispose)
                 (dorun (map (memfn dispose) (vals screens))))
               (pause [])
               (resize [w h]
                 (g/on-resize w h))
               (resume []))]
    (set-var-root #'screens screens)
    (create-lwjgl3-application :title title
                               :game game
                               :width window-width
                               :height window-height
                               :full-screen full-screen)))
