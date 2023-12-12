(ns gdl.app
  (:require [clojure.string :as str]
            [x.x :refer [defcomponent update-map]]
            [gdl.lc :as lc]
            [gdl.graphics.viewport :as viewport]
            [gdl.graphics.shape-drawer :as shape-drawer]
            [gdl.scene2d.ui :as ui])
  (:import (com.badlogic.gdx Gdx ApplicationAdapter)
           com.badlogic.gdx.audio.Sound
           com.badlogic.gdx.assets.AssetManager
           com.badlogic.gdx.files.FileHandle
           com.badlogic.gdx.utils.ScreenUtils
           (com.badlogic.gdx.graphics Color Texture OrthographicCamera)
           com.badlogic.gdx.graphics.g2d.SpriteBatch
           (com.badlogic.gdx.backends.lwjgl3 Lwjgl3Application Lwjgl3ApplicationConfiguration)
           com.badlogic.gdx.utils.SharedLibraryLoader
           (com.badlogic.gdx.utils.viewport Viewport FitViewport)))

(defn render-with [{:keys [^SpriteBatch batch
                           gui-camera
                           world-camera
                           world-unit-scale]
                    :as context}
                   gui-or-world
                   renderfn]
  (let [^OrthographicCamera camera (case gui-or-world
                                     :gui gui-camera
                                     :world world-camera)
        unit-scale (case gui-or-world
                     :gui 1
                     :world world-unit-scale)]
    (shape-drawer/set-line-width unit-scale)
    (.setColor batch Color/WHITE) ; fix scene2d.ui.tooltip flickering
    (.setProjectionMatrix batch (.combined camera))
    (.begin batch)
    (renderfn (assoc context :unit-scale unit-scale))
    (.end batch)
    (shape-drawer/set-line-width 1)))

(defn- update-viewports [{:keys [gui-viewport world-viewport]} w h]
  (let [center-camera? true]
    (.update ^Viewport gui-viewport   w h center-camera?)
    (.update ^Viewport world-viewport w h center-camera?)))

(defn- fix-viewport-update
  "Sometimes the viewport update is not triggered."
  ; TODO (on mac osx, when resizing window, make bug report, fix it in libgdx?)
  [{:keys [^Viewport gui-viewport] :as context}]
  (let [screen-width (.getWidth Gdx/graphics)
        screen-height (.getHeight Gdx/graphics)]
    (when-not (and (= (.getScreenWidth  gui-viewport) screen-width)
                   (= (.getScreenHeight gui-viewport) screen-height))
      (update-viewports context screen-width screen-height))))

(defn- recursively-search-files [folder extensions]
  (loop [[^FileHandle file & remaining] (.list (.internal Gdx/files folder))
         result []]
    (cond (nil? file)
          result

          (.isDirectory file)
          (recur (concat remaining (.list file)) result)

          (extensions (.extension file))
          (recur remaining (conj result (str/replace-first (.path file) folder "")))

          :else
          (recur remaining result))))

(defn- load-assets [^AssetManager manager folder file-extensions ^Class klass log-load-assets?]
  (doseq [file (recursively-search-files folder file-extensions)]
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
                    (.get ^AssetManager this ^String file)))]
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
  (let [batch (SpriteBatch.)
        gui-camera (OrthographicCamera.)
        gui-viewport (FitViewport. (.getWidth Gdx/graphics)
                                   (.getHeight Gdx/graphics)
                                   gui-camera)
        world-unit-scale (/ (or tile-size 1))
        world-camera (OrthographicCamera.)
        world-viewport (let [width  (* (.getWidth Gdx/graphics) world-unit-scale)
                             height (* (.getHeight Gdx/graphics) world-unit-scale)
                             y-down? false]
                         (.setToOrtho world-camera y-down? width height)
                         (FitViewport. width height world-camera))]
    {:batch batch
     :assets (load-all-assets {:folder "resources/" ; TODO these are classpath settings ?
                               :sound-files-extensions #{"wav"}
                               :image-files-extensions #{"png" "bmp"}
                               :log-load-assets? false})

     :gui-camera gui-camera
     :gui-viewport gui-viewport
     :gui-viewport-width  (.getWorldWidth  gui-viewport)
     :gui-viewport-height (.getWorldHeight gui-viewport)

     :world-unit-scale world-unit-scale
     :world-camera world-camera
     :world-viewport world-viewport
     :world-viewport-width  (.getWorldWidth  world-viewport)
     :world-viewport-height (.getWorldHeight world-viewport)

     :gdl.graphics.shape-drawer batch
     ; this is the gdx default skin  - copied from libgdx project, check not included in libgdx jar somewhere?
     :gdl.scene2d.ui (ui/skin (.internal Gdx/files "scene2d.ui.skin/uiskin.json"))}))

(def ^:private state (atom nil))

(defn- update-mouse-positions [context]
  (assoc context
         :gui-mouse-position (mapv int (viewport/unproject-mouse-posi (:gui-viewport context)))
         ; TODO clamping only works for gui-viewport ? check. comment if true
         ; TODO ? "Can be negative coordinates, undefined cells."
         :world-mouse-position (viewport/unproject-mouse-posi (:world-viewport context))))

(defn current-context []
  (update-mouse-positions @state))

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
  (lc/show (current-screen-component)
           (current-context)))

(defn- application-adapter [{:keys [modules first-screen] :as config}]
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
      (let [context (current-context)]
        (fix-viewport-update context)
        (lc/render (current-screen-component) context)
        (lc/tick (current-screen-component)
                 context
                 (* (.getDeltaTime Gdx/graphics) 1000))))
    (resize [w h]
      (update-viewports @state w h))))

(defn- lwjgl3-configuration [{:keys [title width height full-screen? fps]}]
  #_(when SharedLibraryLoader/isMac
      (mac-dock-icon/set-mac-os-dock-icon))
  ; https://github.com/trptr/java-wrapper/blob/39a0947f4e90857512c1999537d0de83d130c001/src/trptr/java_wrapper/locale.clj#L87
  ; cond->
  (let [config (doto (Lwjgl3ApplicationConfiguration.)
                 (.setTitle title)
                 (.setForegroundFPS (or fps 60)))]
    (if full-screen?
      (.setFullscreenMode config (Lwjgl3ApplicationConfiguration/getDisplayMode))
      (.setWindowedMode config width height))
    config))

(defn start [config]
  (Lwjgl3Application. (application-adapter config)
                      (lwjgl3-configuration (:app config))))

(defn pixels->world-units [{:keys [world-unit-scale]} pixels]
  (* pixels world-unit-scale))
