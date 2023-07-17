(defn- draw-texture [texture [x y] [w h] rotation color]
  (if color (.setColor batch color))
  (.draw batch texture
         x
         y
         (/ w 2) ; rotation origin
         (/ h 2)
         w ; width height
         h
         1 ; scaling factor
         1
         rotation)
  (if color (.setColor batch white)))

(defn- unit-dimensions [image]
  (cond
   (= *unit-scale* world-unit-scale) (:world-unit-dimensions  image)
   (= *unit-scale* gui-unit-scale)   (:pixel-dimensions       image)))

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

(defn- texture-dimensions [^TextureRegion texture]
  [(.getRegionWidth  texture)
   (.getRegionHeight texture)])

(def pixel-dimensions :pixel-dimensions)
(def world-unit-dimensions :world-unit-dimensions)

(defn- assoc-dimensions [{:keys [texture scale] :as image}]
  {:pre [(or (number? scale)
             (and (vector? scale)
                  (number? (scale 0))
                  (number? (scale 1))))]}
  (let [pixel-dimensions (if (number? scale)
                           (mapv (partial * scale) (texture-dimensions texture))
                           scale)]
    (assoc image
           :pixel-dimensions pixel-dimensions
           :world-unit-dimensions (mapv (partial * world-unit-scale) pixel-dimensions))))

(defrecord Image [file
                  scale
                  texture
                  pixel-dimensions
                  world-unit-dimensions
                  sub-image-bounds
                  tilew
                  tileh])

(app/defmanaged ^:private get-texture-region
  (memoize
   (fn [file & [x y w h]]
     (let [texture (assets/get-texture file)]
       (if (and x y w h)
         (TextureRegion. texture (int x) (int y) (int w) (int h))
         (TextureRegion. texture))))))

(defn create-image
  "Scale can be a number or [width height]"
  [file & {:keys [scale]}]
  (assoc-dimensions
   (map->Image {:file file
                :scale (or scale 1)
                :texture (get-texture-region file)})))

(defn get-scaled-copy
  "Scaled of original texture-dimensions, not any existing scale."
  [image scale]
  (assoc-dimensions
   (assoc image :scale scale)))

(defn get-sub-image
  "Coordinates are from original image, not scaled one."
  [{:keys [file] :as image} & sub-image-bounds]
  (assoc-dimensions
   (assoc image
          :scale 1
          :texture (apply get-texture-region file sub-image-bounds)
          :sub-image-bounds sub-image-bounds)))

(defn spritesheet [file tilew tileh]
  (assoc (create-image file) :tilew tilew :tileh tileh))

(defn get-sprite [{:keys [tilew tileh] :as sheet} [x y]]
  (get-sub-image sheet (* x tilew) (* y tileh) tilew tileh))

(defn get-sheet-frames [sheet]
  (let [[w h] (:pixel-dimensions sheet)]
    (for [y (range (/ w (:tilew sheet)))
          x (range (/ h (:tileh sheet)))]
      (get-sprite sheet [x y]))))

(defn spritesheet-frames [& args]
  (get-sheet-frames (apply spritesheet args)))

(defprotocol Animation
  (stopped?     [_])
  (restart      [_])
  (get-duration [_])
  (get-frame    [_]))

(defrecord ImmutableAnimation [frames frame-duration looping speed cnt maxcnt]
  Animation
  (stopped? [_]
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
