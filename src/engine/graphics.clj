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

(declare ^:private ^:dynamic *unit-scale*)

(defn pixels [n]
  (* n *unit-scale*))

(defn- set-unit-scale
  "For shape drawer."
  []
  (.setDefaultLineWidth shape-drawer (float *unit-scale*)))

(defn center-rect [^Rectangle rect [x y]]
  (.setCenter rect (float x) (float y)))

(defmulti ^:private draw-shape* class)

(defmethod draw-shape* Circle [^Circle c]
  (.circle shape-drawer (.x c) (.y c) (.radius c)))

(defmethod draw-shape* Rectangle [rect]
  (.rectangle shape-drawer rect))

(defn draw-shape [shape color]
  (set-unit-scale)
  (set-color color)
  (draw-shape* shape))

(defn draw-centered
  ([rectangle posi]
   (draw-centered rectangle posi white))
  ([rectangle posi color]
   (center-rect rectangle posi)
   (set-unit-scale)
   (set-color color)
   (draw-shape rectangle)))

(defn draw-rect
  ([[x y w h] color]
   (draw-rect x y w h color))
  ([x y w h color]
   (set-unit-scale)
   (set-color color)
   (.rectangle shape-drawer x y w h)))

(defn fill-rect
  ([[x y w h] color]
   (fill-rect x y w h color))
  ([x y w h color]
   (set-unit-scale)
   (set-color color)
   (.filledRectangle shape-drawer (float x) (float y) (float w) (float h))))

(defn fill-centered-circle [radius [x y] color]
  (set-unit-scale)
  (set-color color)
  (.filledCircle shape-drawer (float x) (float y) (float radius)))

(defn draw-line
  ([[x y] [ex ey] color]
   (draw-line x y ex ey color))
  ([x y ex ey color]
   (set-unit-scale)
   (set-color color)
   (.line shape-drawer (float x) (float y) (float ex) (float ey))))

(def drawfatline draw-line) ; TODO

; todo bind temporarily unit-scale * 2
; binding?
#_(let [old-scale *unit-scale*]
  (set! *unit-scale* (* 2 old-scale))
  ; do ...
  (set! *unit-scale* old-scale)
  )
#_(defn- draw-fat-line [[x y] [ex ey] color]
    (draw-line x y ex ey color 2))

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

; TODO unit-scale for char-width & char-height
; for rendering on map
; also screen-width & screen-height with shift then ... (ignore for now?)

; alternative font:
; "anuvverbubbla_8x8.png"
; allowed-characters (range 32 91)
; char-width 8
; all text upper-case only

(def ^:private allowed-characters (set (map char (range 32 126))))
(def ^:private starting-character \space)
(def ^:private char-width 6) ; alt: 8
(def ^:private char-height 8)
(def ^:private horizontal-count 94)

(declare ^:private font-spritesheet)

(defn- create-font []
  (set-var-root #'font-spritesheet (spritesheet "simple_6x8.png" 6 8)))

; IMPROVEMENT I could memoize the text->spritesheet xpos or even sprites calculation
; so the texts would be memoized immediately and fast
(defn draw-string [x y text]
  ;{:pre [(every? allowed-characters text)]}
  ; IMPROVEMENT  too strict, just give a warning and put the not allowed char
  (let [data-array (.getBytes ^String text "US-ASCII")]
    (doseq [i (range (alength data-array))
            :let [char-byte (aget data-array i)
                  index (- char-byte (byte starting-character))
                  x-pos (mod index horizontal-count)]]
      ; TODO so many objects .. for each char....
      ; memoize on the spritesheet ?
      (draw-image (get-sprite font-spritesheet [x-pos 0])
                  (+ x (* char-width i))
                  y))))

(defn get-line-height [] char-height)

(defn get-text-height [text]
  (* char-height (count (split-lines text))))

(defn get-text-width [text]
  (* char-width (apply max (map count (split-lines text)))))

(defn- render-colored-text [x y & color-str-seq]
  (loop [y y
         [obj & remaining] color-str-seq]
    (cond
     (instance? Color obj) (do (.setColor *batch* obj)
                               (recur y remaining))

     (string? obj) (if (includes? obj "\n")
                     (recur y
                            (concat (split-lines obj) remaining))
                     (do
                      (draw-string x y obj)
                      (recur (- y (get-line-height))
                             remaining)))))
  (.setColor *batch* white))

; screen-width/screen-height are virtual (see FitViewPort)
; (not the actual window/screen size on the monitor if scaling is applied)
(declare ^:private screen-width
         ^:private screen-height)

(defn- shift-x [x w]
  (cond (> (+ x w) screen-width) (- screen-width w)
        (< x 0) 0
        :else x))

(defn- shift-y [y h]
  (cond (> y screen-height) screen-height
        (< (- y h) 0) (+ y (- (- y h)))
        :else y))

(defcolor transparent-black 0 0 0 0.8)

; TODO FIXME :above does not need to shift the firstline, only subsequent
; TODO kinda confusig that its rendering one line up from x,y and the others down
; either fully above textseq or below ??
; see @ render-item-tooltip adding/removing line height
(defn render-readable-text
  "Renders the first line of text with bottom left corner at x,y.
  The other lines are rendered below."
  [x y
   {:keys [centerx centery above shift background] :as opts
    :or {shift true background true}}
   & color-str-seq]
  (let [color-str-seq (->> color-str-seq
                           (remove nil?)
                           (map #(if (instance? Color %) % (str %))))
        whole-text (->> color-str-seq
                        (remove #(instance? Color %))
                        (interpose "\n")
                        (apply str))
        w (inc (get-text-width whole-text))
        h (get-text-height whole-text)
        x (if centerx (- x (/ w 2)) x)
        y (+ y char-height)
        y (if centery (+ y (/ h 2)) y)
        y (if above (+ y h) y)
        x (if shift (shift-x x w) x)
        y (if shift (shift-y y h) y)
        x (int x)
        y (int y)]
    (when background
      (fill-rect x (- y h) w h transparent-black))
    (apply render-colored-text x (- y char-height) color-str-seq)))

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
         ^:private ^OrthographicCamera map-camera
         ^:private map-viewport
         ^:private sprite-batch)

(defn on-create [width height tile-size]
  (set-var-root #'screen-width width)
  (set-var-root #'screen-height height)

  (set-var-root #'sprite-batch (SpriteBatch.))
  (create-shape-drawer sprite-batch)

  (create-font)

  (set-var-root #'gui-camera (OrthographicCamera.))
  (set-var-root #'gui-viewport (FitViewport. width height gui-camera))

  (set-var-root #'map-camera (OrthographicCamera.))
  (let [map-unit-scale (/ (or tile-size 1))
        width  (* width map-unit-scale)
        height (* height map-unit-scale)]
    (.setToOrtho map-camera false width height)
    (set-var-root #'map-viewport (FitViewport. width height map-camera))))

(defn on-resize [w h]
  (.update gui-viewport w h true)
  (.update map-viewport w h true))

(defn on-dispose []
  (.dispose sprite-batch)
  (dispose-shape-drawer))

(defn- render-with [batch unit-scale ^OrthographicCamera camera renderfn]
  (binding [*batch* batch
            *unit-scale* unit-scale]
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
