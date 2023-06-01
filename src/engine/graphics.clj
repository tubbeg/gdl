(ns engine.graphics
  "* Colors
   * Shape drawer (same batch as image renderer)
   * Images
   * Sprite-sheets
   * Sprite-sheet font renderer
   * Render text in different colors with some formatting
   * Animations
   * GUI and world coordinate systems / cameras
   * FitViewport
   * Rendering to both systems with the respective coordinate systems
    * Shape drawer & image drawer understand the coordinate system
      so I can render shapes at GUI coordinates or world coordinates and it gets rendered properly
   * Rendering tilemap
   * Unproject mouse coordinate to GUI or world coordinates.
   * Tilemap & Image tinting for lights/shadows."
  (:require [clojure.string :refer [includes? split-lines upper-case]]
            [engine.tiled :as tiled]
            [engine.utils :refer [set-var-root get-jar-entries]]
            [engine.asset-manager :as asset-manager])
  (:import [java.io File]
           [com.badlogic.gdx Gdx]
           [com.badlogic.gdx.graphics GL20 OrthographicCamera Color Texture Pixmap Pixmap$Format]
           [com.badlogic.gdx.graphics.g2d Batch SpriteBatch TextureRegion]
           [com.badlogic.gdx.utils.viewport Viewport FitViewport]
           [com.badlogic.gdx.math Vector2 Circle Rectangle MathUtils]
           [space.earlygrey.shapedrawer ShapeDrawer]
           [com.badlogic.gdx.maps MapRenderer]
           [engine OrthogonalTiledMapRendererWithColorSetter ColorSetter]))

;(set! *warn-on-reflection* true)
;(set! *unchecked-math* :warn-on-boxed) ; breaks (byte \char) at draw-string

; IMPROVEMENT: could tag ^Color
(defmacro ^:private defcolors [& names]
  `(do
     ~@(map #(list 'def % (symbol (str "Color/" (upper-case %)))) names)))

(defcolors white yellow red blue green black gray cyan pink orange magenta)

(defn rgbcolor
  ([r g b]
   (rgbcolor r g b 1))
  ([r g b a]
   (Color. (float r) (float g) (float b) (float a))))

(defmacro defcolor [namesym & args]
  `(def ~namesym (rgbcolor ~@args)))

(defn- mul [^Color color value]
  (let [color (.mul (.cpy color) (float value))]
    (set! (.a color) 1)
    color))

(defn multiply-color [^Color color ^Color other]
  (.mul (.cpy color) other))

(defn darker   [color scale] (mul color (- 1 scale)))
(defn brighter [color scale] (mul color (+ 1 scale)))

(declare ^:private ^ShapeDrawer shape-drawer)

(let [shape-drawer-texture (atom nil)]

  (defn- create-shape-drawer [batch]
    (let [pixmap (doto (Pixmap. 1 1 Pixmap$Format/RGBA8888)
                   (.setColor Color/WHITE)
                   (.drawPixel 0 0))
          texture (Texture. pixmap)
          _ (.dispose pixmap)
          region (TextureRegion. texture 0 0 1 1)]
      (reset! shape-drawer-texture texture)
      (set-var-root #'shape-drawer (ShapeDrawer. batch region))))

  (defn- dispose-shape-drawer []
    (.dispose @shape-drawer-texture)))

(defn- set-color
  "For shape drawer."
  [^Color color]
  (.setColor shape-drawer color))

; set to 1 so we can query get-text-width on a text
; outside of rendering function at initialization
(def ^:private ^:dynamic *unit-scale* 1)

(defn pixels [n]
  (* n *unit-scale*))

(defn set-shape-drawer-default-line-width [scale]
  (.setDefaultLineWidth shape-drawer (float (* scale *unit-scale*))))

(defmacro with-shape-drawer-line-width [width & body]
  `(do
    (set-shape-drawer-default-line-width ~width)
    ~@body
    (set-shape-drawer-default-line-width 1)))

(defn draw-ellipse [[x y] radius-x radius-y color]
  (set-color color)
  (.ellipse shape-drawer (float x) (float y) (float radius-x) (float radius-y)))

(defn fill-ellipse [[x y] radius-x radius-y color]
  (set-color color)
  (.filledEllipse shape-drawer (float x) (float y) (float radius-x) (float radius-y)))

(defn draw-circle [[x y] radius color]
  (set-color color)
  (.circle shape-drawer (float x) (float y) (float radius)))

(defn fill-circle [[x y] radius color]
  (set-color color)
  (.filledCircle shape-drawer (float x) (float y) (float radius)))

(defn- degree->radians [degree]
  (* degree (/ (Math/PI) 180)))

(defn draw-arc [[centre-x centre-y] radius start-angle degree color]
  (set-color color)
  (.arc shape-drawer centre-x centre-y radius start-angle (degree->radians degree)))

(defn draw-sector [[centre-x centre-y] radius start-angle degree color]
  (set-color color)
  (.sector shape-drawer centre-x centre-y radius start-angle (degree->radians degree)))

(defn draw-rect
  ([[x y w h] color]
   (draw-rect x y w h color))
  ([x y w h color]
   (set-color color)
   (.rectangle shape-drawer x y w h)))

(defn fill-rect
  ([[x y w h] color]
   (fill-rect x y w h color))
  ([x y w h color]
   (set-color color)
   (.filledRectangle shape-drawer (float x) (float y) (float w) (float h))))

(defn draw-line
  ([[x y] [ex ey] color]
   (draw-line x y ex ey color))
  ([x y ex ey color]
   (set-color color)
   (.line shape-drawer (float x) (float y) (float ex) (float ey))))

(defn draw-grid
  [leftx bottomy gridw gridh cellw cellh color]
  (let [w (* gridw cellw)
        h (* gridh cellh)
        topy (+ bottomy h)
        rightx (+ leftx w)]
    (doseq [idx (range (inc gridw))
            :let [linex (+ leftx (* idx cellw))]]
           (draw-line linex topy linex bottomy color))
    (doseq [idx (range (inc gridh))
            :let [liney (+ bottomy (* idx cellh))]]
           (draw-line leftx liney rightx liney color))))

(defn- texture-dimensions [^TextureRegion texture]
  [(.getRegionWidth texture)
   (.getRegionHeight texture)])

(defn pixel-dimensions [{:keys [texture scale] :as image}]
  (if (number? scale)
    (mapv (partial * scale) (texture-dimensions texture))
    scale))

(declare ^:dynamic ^:private ^Batch *batch*)

; cant call outside as not bound
; if required make defn world-dimensions using world-scale
(defn- unit-dimensions [image]
  (mapv (partial * *unit-scale*) (pixel-dimensions image)))

(defn- draw-texture [texture [x y] [w h] rotation color]
  (if color (.setColor *batch* color))
  (.draw *batch* texture
         x
         y
         (/ w 2) ; rotation origin
         (/ h 2)
         w ; width height
         h
         1 ; scaling factor
         1
         rotation)
  (if color (.setColor *batch* white)))

(defn draw-image
  ([{:keys [texture color] :as image} position]
   (draw-texture texture position (unit-dimensions image) 0 color))
  ([image x y]
   (draw-image image [x y])))

(defn draw-rotated-centered-image
  [{:keys [texture color] :as image} rotation [x y]]
  (let [[w h] (unit-dimensions image)]
    (draw-texture texture
                  [(- x (/ w 2))
                   (- y (/ h 2))]
                  [w h]
                  rotation
                  color)))

(defn draw-centered-image [image position]
  (draw-rotated-centered-image image 0 position))

; IMPROVEMENT
; * make defrecord (faster) (maybe also protocol functions -> faster?)
; * texture can setFilter at Texture$TextureFilter (check scaling ok?)
(defn create-image
  "Scale can be a number or [width height]"
  [file & {:keys [scale]}]
  {:file file
   :scale (or scale 1)
   :texture (asset-manager/file->texture file)})

(defn get-sub-image
  "Coordinates are from original image, not scaled one."
  [{:keys [file] :as image} & sub-image-bounds]
  {:pre [(= 1 (:scale image))]}
  (assoc image
         :texture (apply asset-manager/file->texture file sub-image-bounds)
         :sub-image-bounds sub-image-bounds))

(defn get-scaled-copy
  "Overwrites original scale."
  [image scale]
  (assoc image :scale scale))

(defn spritesheet [file tilew tileh]
  (assoc (create-image file) :tilew tilew :tileh tileh))

(defn get-sprite [{:keys [tilew tileh] :as sheet} [x y]]
  (get-sub-image sheet (* x tilew) (* y tileh) tilew tileh))

(defn get-sheet-frames [sheet]
  (let [[w h] (pixel-dimensions sheet)]
    (for [y (range (/ w (:tilew sheet)))
          x (range (/ h (:tileh sheet)))]
      (get-sprite sheet [x y]))))

(defn spritesheet-frames [& args]
  (get-sheet-frames (apply spritesheet args)))

; alternative font:
; "anuvverbubbla_8x8.png"
; allowed-characters (range 32 91)
; char-width 8
; all text upper-case only

(def ^:private allowed-characters (set (map char (range 32 126))))
(def ^:private starting-character \space)
(def ^:private char-width-px 6)
(def ^:private char-height-px 8)
(def ^:private horizontal-count 94)

(defn- char-width []
  (* char-width-px *unit-scale*))

(defn- char-height []
  (* char-height-px *unit-scale*))

(declare ^:private font-spritesheet)

(defn- create-font []
  (set-var-root #'font-spritesheet (spritesheet "simple_6x8.png" 6 8)))

; IMPROVEMENT I could memoize the text->spritesheet xpos or even sprites calculation
; so the texts would be memoized immediately and fast
(defn- draw-string
  "Draws the string at position x,y.
  Does not support formatting, centering, shifting, background like
  render-readable-text."
  [x y string scale]
  ;{:pre [(every? allowed-characters string)]}
  ; IMPROVEMENT  too strict, just give a warning and put the not allowed char
  (let [data-array (.getBytes ^String string "US-ASCII")]
    (doseq [i (range (alength data-array))
            :let [char-byte (aget data-array i)
                  index (- char-byte (byte starting-character))
                  x-pos (mod index horizontal-count)
                  char-sprite (get-sprite font-spritesheet [x-pos 0])
                  char-sprite (if (not= scale 1)
                                (get-scaled-copy char-sprite scale)
                                char-sprite)
                  char-width (* scale (char-width))]]
      (draw-image char-sprite
                  (+ x (* char-width i))
                  y))))

;; A 'textseq' here is a sequence of Color or strings (and nils are also allowed, will be ignored)
;; where colors will be set for subsequent strings and
;; after each element a newline will be inserted
;; strings can also contain newlines \n where a newline will be inserted
;; and in metadata can have :scale key

(def ^:private default-font-scale 2)

(defn- scale
  "Text is a textseq or a string."
  [text]
  (or (:scale (meta text))
      default-font-scale))

(defn- line-height
  "Text is a textseq or a string."
  [text]
  (* (char-height) (scale text)))

(defn- textseq->text-lines [textseq]
  (->> textseq
       (remove #(instance? Color %))
       (interpose "\n")
       (apply str)
       split-lines))

(defn- ->textseq
  "Text is a textseq or a string."
  [text]
  (if (string? text) [text] text))

(defn get-text-height
  "Text is a textseq or a string."
  [text]
  (* (line-height text)
     (count (textseq->text-lines (->textseq text)))))

; should work with nil's and Colors in the textseq
(defn get-text-width
  "Text is a textseq or a string."
  [text]
  (* (char-width)
     (apply max (map count (textseq->text-lines (->textseq text))))
     (scale text)))

(defn- render-text* [x y textseq]
  (loop [y (+ y
              (get-text-height textseq)
              (- (line-height textseq)))
         [obj & remaining] textseq]
    (cond
     (instance? Color obj) (do (.setColor *batch* obj)
                               (recur y remaining))

     (string? obj) (if (includes? obj "\n")
                     (recur y
                            (concat (split-lines obj) remaining))
                     (do
                      (draw-string x y obj (:scale (meta textseq)))
                      (recur (- y (line-height textseq))
                             remaining)))))
  (.setColor *batch* white))

; screen-width/screen-height are virtual (see FitViewPort)
; (not the actual window/screen size on the monitor if scaling is applied)
; TODO FIXME == viewport-width / height !
(declare ^:private screen-width
         ^:private screen-height)

; Shift in world coordinate system:
; text will be inside the map tiles (not less than 0)
; problems if world size > screen-width
; then text would not be rendered at right position

(defn- shift-x [x w]
  (cond (> (+ x w) screen-width) (- screen-width w)
        (< x 0) 0
        :else x))

(defn- shift-y [y h]
  (cond (> (+ y h) screen-height) (- screen-height h)
        (< y 0) 0
        :else y))

(defcolor transparent-black 0 0 0 0.8)

(defn render-readable-text
  "Renders a block of text with bottom left corner at x,y.
  The other lines are rendered below.
  textseq is a sequence of colors or strings. A color will set the color
  for the subsequent strings and each separate string element will be drawn
  below the last. Strings can also contain \n element for that.
  Textseq can also be just one element.
  Do not use :shift in world coordinate system."
  [x y
   {:keys [centerx centery shift background] :as opts
    :or {shift true background true}}
   textseq]
  (let [textseq (if (coll? textseq) textseq [textseq])
        scl (scale textseq) ; gets lost in the next form
        textseq (->> textseq
                     (remove nil?)
                     (map #(if (instance? Color %) % (str %))))
        textseq (with-meta textseq {:scale scl})
        w (get-text-width textseq)
        h (get-text-height textseq)
        x (if centerx (- x (/ w 2)) x)
        y (if centery (- y (/ h 2)) y)
        x (if shift (shift-x x w) x)
        y (if shift (shift-y y h) y)]
    (when background
      (fill-rect x y w h transparent-black))
    (render-text* x y textseq)))

(defprotocol Animation
  (is-stopped?  [_])
  (restart      [_])
  (get-duration [_])
  (get-frame    [_]))

; AnimationHash(Map)
(defrecord ImmutableAnimation [frames frame-duration looping speed cnt maxcnt]
  Animation
  (is-stopped? [_]
    (and (not looping) (= cnt maxcnt)))
  (restart [this]
    (assoc this :cnt 0))
  (get-duration [_]
    maxcnt)
  (get-frame [this]
    ; int because cnt can be a float value
    (get frames (int (quot (dec cnt) frame-duration)))))

(defn update-animation [{:keys [cnt speed maxcnt looping] :as this} delta]
  (let [newcnt (+ cnt (* speed delta))]
    (assoc this :cnt (cond (< newcnt maxcnt) newcnt
                           looping           (min maxcnt (- newcnt maxcnt))
                           :else             maxcnt))))

(def default-frame-duration 33)

(defn create-animation
  [frames & {:keys [frame-duration looping] :or {frame-duration default-frame-duration}}]
  (map->ImmutableAnimation
    {:frames (vec frames)
     :frame-duration frame-duration
     :looping looping
     :speed 1
     :cnt 0
     :maxcnt (* (count frames) frame-duration)}))

(defn render-centered-animation [animation position]
  (draw-centered-image (get-frame animation) position))

(let [debug false
      already-printed (atom #{})]
  (defn- debug-print-result [folder prefix result]
    (when debug
      (when-not (contains? @already-printed [folder prefix])
        (swap! already-printed conj [folder prefix])
        (println "\n" [folder prefix] " : " result)))))

(defn- filter-prefix-and-sort [names prefix]
  (sort (if prefix
          (filter #(.startsWith ^String % prefix) names)
          names)))

(let [all-png-entries (get-jar-entries #(.endsWith ^String % ".png"))]

  (defn get-sorted-pngs-in-jar [folder & {prefix :prefix}]
    (let [hits (filter #(.startsWith ^String % folder) all-png-entries)
          names (map #(subs % (inc (.lastIndexOf ^String % "/"))) hits)
          result (filter-prefix-and-sort names prefix)]
      (assert (apply = (map #(.lastIndexOf ^String % "/") hits)))
      (debug-print-result folder prefix result)
      result)))

"
entryname:
data/player/shooting/shoot0.png
data/player/shooting/shoot1.png
data/player/shooting/raw/weapon.png

startswith: data/player/shooting/
endswith: .png

result includes weapon.png

how to filter /raw ?
-> filter out if between starts and ends is another slash / ?
assert lastindexOf slash is the same for names in a folder?
"

(defn- get-sorted-pngs [folder & {prefix :prefix}]
  (let [file (File. ^String (str "resources/" folder))
        listed-files (.listFiles file)
        pngs (filter #(.endsWith (.getPath ^File %) ".png") listed-files)
        names (map #(.getName ^File %) pngs)
        result (filter-prefix-and-sort names prefix)]
    (debug-print-result folder prefix result)
    result))

(def get-pngs (if false #_jar-file? get-sorted-pngs-in-jar get-sorted-pngs))

(defn folder-frames [folder & {:keys [prefix]}]
  (doall (map #(create-image (str folder %)) (get-pngs folder :prefix prefix))))

(defn folder-animation
  "duration is duration of all frames together, will be split evenly across frames."
  [& {:keys [folder looping duration prefix]}]
  (let [frames (folder-frames folder :prefix prefix)]
    (create-animation frames
                      :frame-duration (if duration
                                        (int (/ duration (count frames)))
                                        default-frame-duration)
                      :looping looping)))

(declare ^:private gui-camera
         ^:private gui-viewport
         ^:private map-unit-scale
         ^:private ^OrthographicCamera map-camera
         ^:private map-viewport
         ^:private sprite-batch)

(defn initialize [width height tile-size] ; TODO rename to viewport-width / viewport-height
  (set-var-root #'screen-width width) ; TODO also rename then
  (set-var-root #'screen-height height)

  (set-var-root #'sprite-batch (SpriteBatch.))
  (create-shape-drawer sprite-batch)

  (create-font)

  (set-var-root #'gui-camera (OrthographicCamera.))
  (set-var-root #'gui-viewport (FitViewport. width height gui-camera))

  (set-var-root #'map-unit-scale (/ (or tile-size 1)))
  (set-var-root #'map-camera (OrthographicCamera.))
  (let [width  (* width map-unit-scale)
        height (* height map-unit-scale)]
    (.setToOrtho map-camera false width height)
    (set-var-root #'map-viewport (FitViewport. width height map-camera))))

(defn on-resize [w h]
  (.update gui-viewport w h true)
  (.update map-viewport w h true))

(defn- fix-viewport-update
  "Sometimes the viewport update is not triggered."
  []
  (let [screen-width (.getWidth (Gdx/graphics))
        screen-height (.getHeight (Gdx/graphics))]
    (if (or (not= (.getScreenWidth gui-viewport) screen-width)
            (not= (.getScreenHeight gui-viewport) screen-height))
      (on-resize screen-width screen-height))))

(defn on-update []
  (fix-viewport-update))

(defn on-dispose []
  (.dispose sprite-batch)
  (dispose-shape-drawer))

(defn- render-with [batch unit-scale ^OrthographicCamera camera renderfn]
  (binding [*batch* batch
            *unit-scale* unit-scale]
    (set-shape-drawer-default-line-width 1)
    (.setProjectionMatrix *batch* (.combined camera))
    (.begin *batch*)
    (renderfn)
    (.end *batch*)))

(defn render-gui-level [renderfn]
  (render-with sprite-batch 1 gui-camera renderfn))

(defn render-map-level [renderfn]
  (render-with sprite-batch map-unit-scale map-camera renderfn))

; OrthogonalTiledMapRenderer extends BatchTiledMapRenderer
; and when a batch is passed to the constructor
; we do not need to dispose the renderer
(defn- map-renderer-for [tiled-map color-setter]
  (OrthogonalTiledMapRendererWithColorSetter. tiled-map
                                              (float map-unit-scale)
                                              sprite-batch
                                              (reify ColorSetter
                                                (apply [_ color x y]
                                                  (color-setter color x y)))))

(def ^:private cached-map-renderer (memoize map-renderer-for))

(defn render-map [tiled-map color-setter [x y] layers]
  (set! (.x (.position map-camera)) x)
  (set! (.y (.position map-camera)) y)
  (.update map-camera)
  (let [^MapRenderer map-renderer (cached-map-renderer tiled-map color-setter)]
    (.setView map-renderer map-camera)
    (->> layers
         (map (partial tiled/layer-index tiled-map))
         int-array
         (.render map-renderer))))

(defn- clamp [value min max]
  (MathUtils/clamp (float value) (float min) (float max)))

; touch coordinates are y-down, while screen coordinates are y-up
; so the clamping of y is reverse, but as black bars are equal it does not matter
(defn- unproject-mouse-posi [^Viewport viewport]
  (let [mouse-x (clamp (.getX (Gdx/input))
                       (.getLeftGutterWidth viewport)
                       (.getRightGutterX viewport))
        mouse-y (clamp (.getY (Gdx/input))
                       (.getTopGutterHeight viewport)
                       (.getTopGutterY viewport))
        coords (.unproject viewport (Vector2. mouse-x mouse-y))]
    [(.x coords) (.y coords)]))

(defn mouse-coords [] ; TODO screen-coords (gui-coords)
  (mapv int (unproject-mouse-posi gui-viewport)))

(defn map-coords ; or 'world-mouse-posi'
  "Can be negative coordinates, undefined cells." ; TODO check if true
  []
  (unproject-mouse-posi map-viewport))

(defn clear-screen [] ; TODO use clear screen utils
  (.glClearColor (Gdx/gl) 0 0 0 1)
  (.glClear (Gdx/gl) GL20/GL_COLOR_BUFFER_BIT))

(defn viewport-width  [] (.getWorldWidth  gui-viewport))
(defn viewport-height [] (.getWorldHeight gui-viewport))

(defn world-viewport-width  [] (.getWorldWidth  map-viewport))
(defn world-viewport-height [] (.getWorldHeight map-viewport))
