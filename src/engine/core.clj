(ns engine.core
  (:require [engine.utils :refer (set-var-root)]
            [engine.graphics :as g])
  (:import [com.badlogic.gdx.backends.lwjgl3 Lwjgl3Application Lwjgl3ApplicationConfiguration]
           [com.badlogic.gdx Gdx Screen Game]))

(defn ^:private create-lwjgl3-application
  [& {:keys [title game width height full-screen]}]
  (let [config (Lwjgl3ApplicationConfiguration.)]
    (.setTitle config title)
    (.useVsync config true)
    (if full-screen
      (.setFullscreenMode config (Lwjgl3ApplicationConfiguration/getDisplayMode))
      (.setWindowedMode config width height))
    (println "Starting Lwjgl3Application")
    (Lwjgl3Application. game config)))

(defn exit-app []
  (.exit (Gdx/app)))

(defmacro with-context [& body]
   `(.postRunnable (Gdx/app)
                   (fn [] ~@body)))

(defn get-fps []
  (str (.getFramesPerSecond (Gdx/graphics))))

;;

; TODO does not work with refresh ! -> remove ...
; make lifecycle hashes & collect them manually
(def ^:private init-fns [])

; TODO add 'destroy' also for disposing (reloaded workflow)
; on-create
; with-graphics-context
(defmacro initialize
  "Use for initializing objects inside the game loop thread."
   [& exprs]
  `(alter-var-root #'engine.core/init-fns conj
                   (fn [] ~@exprs)))

(defn init-all []
  (doseq [f init-fns]
    (f)))

; Pre-load big images so the game does not pause/lag when they are played for the first time
; even more important when those images are played only one time for example big monster explosion
; TODO AssetManager?
; TODO def-game -> calls .dispose automatically on the object ?!
(defmacro defpreload [& more]
  `(initialize (def ~@more)))

; TODO or GameLifeCycleObjects
; - on-create: (set-var-root sprite-batch (SpriteBatch.))
; - on-dispose (.dispose sprite-batch)
; - on-update ?
; - on-resize (not necessary yet (only for viewport, skip for now)

; (defimage test-image "res/foobar" :scale [1 2])
; (defspritesheet ...)

; game :assets -> [test-image test-spritesheet]

; assets -> load

;;

(defprotocol GameScreen
  "A game can have different screens like main-menu, player-selection, actual ingame-state, and so on.
  Graphics context is available in all functions for loading/disposing of resources."
  (show [this]
        "Called each time this screen is shown.")
  (destroy [this]
           "Called once on closing the game app")
  (render [this]
          "Called on every tick before update-screen")
  (update-screen [this delta]
                 "Called on every tick with elapsed delta time in ms"))

(defn- game-screen->libgdx-screen [game-screen]
  (reify Screen
    (show [_]
      (show game-screen))
    (render [_ delta]
      (g/clear-screen)
      ; TODO check if resize happened and resize was not called (maximize, or move window)
      ; compare screen width to viewport set screenwidth size maybe
      (render game-screen)
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
  [& {:keys [game-screens
             full-screen
             title
             window-width
             window-height
             viewport-width
             viewport-height
             assets-folder]
      :or {title "Test"
           window-width 800
           window-height 600
           viewport-width 800
           viewport-height 600}}]
  (let [screens (zipmap
                 (keys game-screens)
                 (map game-screen->libgdx-screen (vals game-screens)))
        game (proxy [Game] []
               (create []
                 (g/on-create viewport-width viewport-height assets-folder)
                 (init-all)
                 (.setScreen this (first (vals screens))))
               (dispose []
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

(defn fullscreen-supported?
  ([w h] false)
  ([] false)) ;  	(.supportsDisplayModeChange (Gdx/graphics))

; TODO asset manager loads all sounds in 'sounds/' folder
; play-sound just (.play (.get manager (str "sounds/" sound) SoundClass))

(defn create-sound [spath]
  )

(defn play-sound [spath]
  )

(defn playonce [sound]
  ;(when-not (.playing sound)
  ;  (.play sound))
  )

;(defn set-mouse-cursor [data hotspotx hotspoty]
;  (.setMouseCursor app-game-container data hotspotx hotspoty))

; TODO counter does not belong here

; TODO there is one more counter in game.utils.core
(defrecord ImmutableCounter [cnt maxcnt stopped?])

(defn make-counter [maxcnt]
  (ImmutableCounter. 0 maxcnt false))

(defn tick [{:keys [cnt maxcnt stopped?] :as this} delta]
  (let [newcnt   (+ cnt delta)
        stopped? (>= newcnt maxcnt)]
    (assoc this
           :cnt (if stopped? (- newcnt maxcnt) newcnt)
           :stopped? stopped?)))

; if (> maxdelta maxcnt) it could happen that after update it is again 'stopped?' in next update
; could assert (<= maxcnt maxdelta), but dont want to depend on game.components.update here.

(defn ratio [{:keys [cnt maxcnt]}]
  (/ cnt maxcnt))

; TODO rename tick-and-merge-on-stopped
(defn update-finally-merge [m counter-key delta merge-map]
  (let [m (update m counter-key tick delta)]
    (if (:stopped? (counter-key m))
      (merge m merge-map)
      m)))

(defn reset [counter]
  (assoc counter :cnt 0))
