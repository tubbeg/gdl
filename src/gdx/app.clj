(ns gdx.app
  (:require [gdx.utils :refer (set-var-root)]
            [gdx.mac-dock-icon :as mac-dock-icon])
  (:import [com.badlogic.gdx.backends.lwjgl3 Lwjgl3Application Lwjgl3ApplicationConfiguration]
           [com.badlogic.gdx.utils SharedLibraryLoader Disposable]
           [com.badlogic.gdx Gdx Application]))

(defn- lwjgl-config [{:keys [title width height full-screen fps]}]
  #_(when SharedLibraryLoader/isMac
      (mac-dock-icon/set-mac-os-dock-icon))

  (let [config (doto (Lwjgl3ApplicationConfiguration.)
                 (.setTitle title)
                 (.setForegroundFPS (or fps 60)))]
    (if full-screen
      (.setFullscreenMode config (Lwjgl3ApplicationConfiguration/getDisplayMode))
      (.setWindowedMode config width height))
    config))

(defn create [game config]
  (Lwjgl3Application. game (lwjgl-config config)))

(def ^:private on-create-fns  [])
(def ^:private on-destroy-fns [])

(defmacro on-create  [& exprs] `(alter-var-root #'on-create-fns  conj (fn [] ~@exprs)))
(defmacro on-destroy [& exprs] `(alter-var-root #'on-destroy-fns conj (fn [] ~@exprs)))

(defn ^:no-doc call-on-create-fns!  [] (doseq [f on-create-fns]  (f)))
(defn ^:no-doc call-on-destroy-fns! [] (doseq [f on-destroy-fns] (f)))

(defn ^:no-doc dispose [^Disposable obj] (.dispose obj))

(defmacro defmanaged [symbol init]
  `(do
    (declare ~symbol)
    (let [var# (var ~symbol)]
      (on-create (set-var-root var# ~init))
      (on-destroy (when (:dispose (meta var#)) (dispose ~symbol))))))

(defmanaged ^:no-doc ^Application app Gdx/app)

(defn destroy [] (.exit app))

(defmacro with-context [& exprs]
  `(.postRunnable app (fn [] ~@exprs)))
