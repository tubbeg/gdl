(ns gdl.app
  (:require [x.x :refer [defcomponent update-map]]
            [gdl.lc :as lc]
            [gdl.graphics :as g]
            [gdl.files :as files]
            gdl.graphics.shape-drawer
            [gdl.graphics.gui :as gui]
            [gdl.graphics.world :as world]
            [gdl.scene2d.ui :as ui]
            [gdl.backends.lwjgl3 :as lwjgl3])
  (:import (com.badlogic.gdx Gdx Application ApplicationAdapter)
           com.badlogic.gdx.audio.Sound
           com.badlogic.gdx.assets.AssetManager
           com.badlogic.gdx.utils.ScreenUtils
           (com.badlogic.gdx.graphics Color Texture)
           com.badlogic.gdx.graphics.g2d.SpriteBatch))

(defn exit []
  (.exit Gdx/app))

(defmacro with-context [& exprs]
  `(.postRunnable Gdx/app (fn [] ~@exprs)))

(defn- on-resize [w h]
  (let [center-camera? true]
    (.update gui/viewport   w h center-camera?)
    (.update world/viewport w h center-camera?)))

(defn- fix-viewport-update
  "Sometimes the viewport update is not triggered."
  []
  (when-not (and (= (.getScreenWidth  gui/viewport) (g/screen-width))
                 (= (.getScreenHeight gui/viewport) (g/screen-height)))
    (on-resize (g/screen-width) (g/screen-height))))

(defn- load-assets [^AssetManager manager folder file-extensions ^Class klass log-load-assets?]
  (doseq [file (files/recursively-search-files folder file-extensions)]
    (when log-load-assets?
      (println "load-assets" (str "[" (.getSimpleName klass) "] - [" file "]")))
    (.load manager file klass)))

(defn- load-all-assets [{:keys [folder
                                log-load-assets?
                                sound-files-extensions
                                image-files-extensions]
                         :as config}]
  (doseq [k [:folder
             :log-load-assets?
             :sound-files-extensions
             :image-files-extensions]]
    (assert (contains? config k)
            (str "config key(s) missing: " k)))
  (let [manager (proxy [AssetManager clojure.lang.ILookup] []
                  (valAt [file]
                    (.get this ^String file)))]
    (load-assets manager folder sound-files-extensions Sound   log-load-assets?)
    (load-assets manager folder image-files-extensions Texture log-load-assets?)
    (.finishLoading manager)
    manager))

(defcomponent :batch batch
  (lc/dispose [_]
    (.dispose ^SpriteBatch batch)))

(defcomponent :assets manager
  (lc/dispose [_]
    (.dispose ^AssetManager manager)))

(defn- default-components [{:keys [tile-size]}]
  (let [batch (SpriteBatch.)]
    {:batch batch
     :assets (load-all-assets {:folder "resources/" ; TODO these are classpath settings ?
                               :sound-files-extensions #{"wav"}
                               :image-files-extensions #{"png" "bmp"}
                               :log-load-assets? false})
     ; TODO add viewports/cameras here FitViewport user-choice !
     :gdl.graphics.gui nil
     :gdl.graphics.world (or tile-size 1)
     :gdl.graphics.shape-drawer batch
     ; this is the gdx default skin  - copied from libgdx project, check not included in libgdx jar somewhere?
     :gdl.scene2d.ui (ui/skin (files/internal "scene2d.ui.skin/uiskin.json"))}))

(def state (atom nil))

(defn- current-screen-component []
  (let [k (::current-screen @state)]
    [k (k @state)]))

(defn current-screen-value []
  ((::current-screen @state) @state))

(defn set-screen [k]
  (assert (contains? @state k) (str "Cannot find screen with key: " k " in state."))
  (when (::current-screen @state)
    (lc/hide (current-screen-component)))
  (swap! state assoc ::current-screen k)
  (lc/show (current-screen-component)))

(defn- application-adapter [{:keys [log-lc? modules first-screen] :as config}]
  (proxy [ApplicationAdapter] []
    (create []
      (reset! state
              (let [context (update-map (default-components config) lc/create nil)]
                (merge context
                       (update-map modules lc/create context))))
      (set-screen first-screen))
    (dispose []
      (swap! state update-map lc/dispose))
    (render []
      (ScreenUtils/clear Color/BLACK)
      (fix-viewport-update)
      (lc/render (current-screen-component) @state)
      (lc/tick (current-screen-component)
               @state
               (* (.getDeltaTime Gdx/graphics) 1000)))
    (resize [w h]
      (on-resize w h))))

(defn start [{:keys [window] :as config}]
  (lwjgl3/create-app (application-adapter config)
                     window))
