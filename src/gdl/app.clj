(ns gdl.app
  (:require [clojure.string :as str]
            [gdl.screen :as screen]
            [gdl.protocols :refer [dispose]]
            gdl.graphics.freetype
            gdl.context.text-drawer
            gdl.context.image-drawer-creator
            gdl.scene2d.ui)
  (:import (com.badlogic.gdx Gdx ApplicationAdapter)
           com.badlogic.gdx.audio.Sound
           com.badlogic.gdx.assets.AssetManager
           (com.badlogic.gdx.backends.lwjgl3 Lwjgl3Application Lwjgl3ApplicationConfiguration)
           com.badlogic.gdx.files.FileHandle
           (com.badlogic.gdx.graphics Color Texture OrthographicCamera Pixmap Pixmap$Format)
           (com.badlogic.gdx.graphics.g2d Batch SpriteBatch TextureRegion)
           com.badlogic.gdx.utils.ScreenUtils
           (com.badlogic.gdx.utils.viewport Viewport FitViewport)
           [com.badlogic.gdx.math Vector2 MathUtils]
           space.earlygrey.shapedrawer.ShapeDrawer))

(defn- degree->radians [degree]
  (* degree (/ (Math/PI) 180)))

(extend-type gdl.protocols.Context
  gdl.protocols/ShapeDrawer
  (draw-ellipse [{:keys [^ShapeDrawer shape-drawer]} [x y] radius-x radius-y color]
    (.setColor shape-drawer ^Color color)
    (.ellipse shape-drawer (float x) (float y) (float radius-x) (float radius-y)) )

  (draw-filled-ellipse [{:keys [^ShapeDrawer shape-drawer]} [x y] radius-x radius-y color]
    (.setColor shape-drawer ^Color color)
    (.filledEllipse shape-drawer (float x) (float y) (float radius-x) (float radius-y)))

  (draw-circle [{:keys [^ShapeDrawer shape-drawer]} [x y] radius color]
    (.setColor shape-drawer ^Color color)
    (.circle shape-drawer (float x) (float y) (float radius)))

  (draw-filled-circle [{:keys [^ShapeDrawer shape-drawer]} [x y] radius color]
    (.setColor shape-drawer ^Color color)
    (.filledCircle shape-drawer (float x) (float y) (float radius)))

  (draw-arc [{:keys [^ShapeDrawer shape-drawer]} [centre-x centre-y] radius start-angle degree color]
    (.setColor shape-drawer ^Color color)
    (.arc shape-drawer centre-x centre-y radius start-angle (degree->radians degree)))

  (draw-sector [{:keys [^ShapeDrawer shape-drawer]} [centre-x centre-y] radius start-angle degree color]
    (.setColor shape-drawer ^Color color)
    (.sector shape-drawer centre-x centre-y radius start-angle (degree->radians degree)))

  (draw-rectangle [{:keys [^ShapeDrawer shape-drawer]} x y w h color]
    (.setColor shape-drawer ^Color color)
    (.rectangle shape-drawer x y w h) )

  (draw-filled-rectangle [{:keys [^ShapeDrawer shape-drawer]} x y w h color]
    (.setColor shape-drawer ^Color color)
    (.filledRectangle shape-drawer (float x) (float y) (float w) (float h)) )

  (draw-line [this [x y] [ex ey] color]
    (gdl.protocols/draw-line this x y ex ey color))

  (draw-line [{:keys [^ShapeDrawer shape-drawer]} x y ex ey color]
    (.setColor shape-drawer ^Color color)
    (.line shape-drawer (float x) (float y) (float ex) (float ey)))

  (draw-grid [this leftx bottomy gridw gridh cellw cellh color]
    (let [w (* gridw cellw)
          h (* gridh cellh)
          topy (+ bottomy h)
          rightx (+ leftx w)]
      (doseq [idx (range (inc gridw))
              :let [linex (+ leftx (* idx cellw))]]
        (gdl.protocols/draw-line this linex topy linex bottomy color))
      (doseq [idx (range (inc gridh))
              :let [liney (+ bottomy (* idx cellh))]]
        (gdl.protocols/draw-line this leftx liney rightx liney color))))

  (with-shape-line-width [{:keys [^ShapeDrawer shape-drawer]} width draw-fn]
    (let [old-line-width (.getDefaultLineWidth shape-drawer)]
      (.setDefaultLineWidth shape-drawer (float (* width old-line-width)))
      (draw-fn)
      (.setDefaultLineWidth shape-drawer (float old-line-width)))))

(defn render-view [{:keys [^Batch batch
                           shape-drawer
                           gui-camera
                           world-camera
                           world-unit-scale]
                    :as context}
                   gui-or-world
                   draw-fn]
  (let [^OrthographicCamera camera (case gui-or-world
                                     :gui gui-camera
                                     :world world-camera)
        unit-scale (case gui-or-world
                     :gui 1
                     :world world-unit-scale)
        context (assoc context :unit-scale unit-scale)]
    (.setColor batch Color/WHITE) ; fix scene2d.ui.tooltip flickering
    (.setProjectionMatrix batch (.combined camera))
    (.begin batch)
    (gdl.protocols/with-shape-line-width context unit-scale #(draw-fn context))
    (.end batch)))

(defn- update-viewports [{:keys [gui-viewport world-viewport]} w h]
  (.update ^Viewport gui-viewport   w h true)
  ; Do not center the camera on world-viewport. We set the position there manually.
  (.update ^Viewport world-viewport w h false))

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
    (cond (nil? file) result
          (.isDirectory file) (recur (concat remaining (.list file)) result)
          (extensions (.extension file)) (recur remaining (conj result (str/replace-first (.path file) folder "")))
          :else (recur remaining result))))

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

; TODO ! all keywords add namespace ':context/'
(defn- default-components [{:keys [tile-size]}]
  (let [batch (SpriteBatch.)]
    (merge {:batch batch
            :unit-scale 1
            :assets (load-all-assets {:folder "resources/" ; TODO these are classpath settings ?
                                      :sound-files-extensions #{"wav"}
                                      :image-files-extensions #{"png" "bmp"}
                                      :log-load-assets? false})
            :context/scene2d.ui (gdl.scene2d.ui/initialize!)}

           (gdl.context.text-drawer/->context-map)

           ; separate ns -> loads shapedrawer protocol on context class (which I maybe pass there ? )
           ; disposable -> only 1 new context component
           ; also namespaced name ?
           (let [texture (let [pixmap (doto (Pixmap. 1 1 Pixmap$Format/RGBA8888)
                                        (.setColor Color/WHITE)
                                        (.drawPixel 0 0))
                               texture (Texture. pixmap)]
                           (.dispose pixmap)
                           texture)]
             {:shape-drawer (ShapeDrawer. batch (TextureRegion. texture 0 0 1 1))
              :shape-drawer-texture texture})

           ; create views manually ...
           (let [gui-camera (OrthographicCamera.)
                 gui-viewport (FitViewport. (.getWidth Gdx/graphics)
                                            (.getHeight Gdx/graphics)
                                            gui-camera)]
             {:gui-camera   gui-camera
              :gui-viewport gui-viewport
              :gui-viewport-width  (.getWorldWidth  gui-viewport)
              :gui-viewport-height (.getWorldHeight gui-viewport)})

           ; create views ....
           (let [world-camera (OrthographicCamera.)
                 world-unit-scale (/ (or tile-size 1))
                 world-viewport (let [width  (* (.getWidth Gdx/graphics) world-unit-scale)
                                      height (* (.getHeight Gdx/graphics) world-unit-scale)
                                      y-down? false]
                                  (.setToOrtho world-camera y-down? width height)
                                  (FitViewport. width height world-camera))]
             {:world-unit-scale world-unit-scale
              :world-camera     world-camera
              :world-viewport   world-viewport
              :world-viewport-width  (.getWorldWidth  world-viewport)
              :world-viewport-height (.getWorldHeight world-viewport)}))))

(defn- clamp [value min max]
  (MathUtils/clamp (float value) (float min) (float max)))

; touch coordinates are y-down, while screen coordinates are y-up
; so the clamping of y is reverse, but as black bars are equal it does not matter
(defn- unproject-mouse-posi [^Viewport viewport]
  (let [mouse-x (clamp (.getX Gdx/input)
                       (.getLeftGutterWidth viewport)
                       (.getRightGutterX viewport))
        mouse-y (clamp (.getY Gdx/input)
                       (.getTopGutterHeight viewport)
                       (.getTopGutterY viewport))
        coords (.unproject viewport (Vector2. mouse-x mouse-y))]
    [(.x coords) (.y coords)]))

; maybe functions 'mouse-position' on 'view' ?
(defn- update-mouse-positions [context]
  (assoc context
         :gui-mouse-position (mapv int (unproject-mouse-posi (:gui-viewport context)))
         ; TODO clamping only works for gui-viewport ? check. comment if true
         ; TODO ? "Can be negative coordinates, undefined cells."
         :world-mouse-position (unproject-mouse-posi (:world-viewport context))))

(def state (atom nil)) ; TODO rename context?

(defn current-context []
  (update-mouse-positions @state))

; TODO here not current-context .... should not do @state or get mouse-positions via function call
; but then keep unprojecting ?
; TODO TEST current logic of that screen will be continued ?
(defn change-screen! [new-screen-key]
  (let [{:keys [context/current-screen] :as context} @state]
    (when-let [previous-screen (get context current-screen)]
      (screen/hide previous-screen context))
    (let [new-screen (new-screen-key context)]
      (assert new-screen (str "Cannot find screen with key: " new-screen-key))
      (swap! state assoc :context/current-screen new-screen-key)
      (screen/show new-screen @state))))

(defn- dispose-context [context]
  (doseq [[k value] context]
    (cond (extends? gdl.protocols/Disposable (class value))
          (do
           (println "Disposing " k)
           (dispose value))
          ((supers (class value)) com.badlogic.gdx.utils.Disposable)
          (do
           (println "Disposing " k)
           (.dispose ^com.badlogic.gdx.utils.Disposable value)))))

(defn- application-adapter [{:keys [modules first-screen] :as config}]
  (proxy [ApplicationAdapter] []
    (create []
      ; TODO let completely the user do this
      (let [context (-> config
                        default-components
                        gdl.protocols/map->Context)
            context (merge context (modules context))]  ; TODO safe-merge ?
        (reset! state context))
      (change-screen! first-screen))
    (dispose []
      (dispose-context @state))
    (render []
      (ScreenUtils/clear Color/BLACK)
      (let [{:keys [context/current-screen] :as context} (current-context)
            screen (current-screen context)]
        (fix-viewport-update context)
        (screen/render screen context)
        (screen/tick screen context (* (.getDeltaTime Gdx/graphics) 1000))))
    (resize [w h]
      ; TODO here also @state and not current-context ...
      (update-viewports @state w h))))

(defn- lwjgl3-configuration [{:keys [title width height full-screen? fps]}]
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
