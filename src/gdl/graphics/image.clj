(ns gdl.graphics.image
  (:require [gdl.assets :as assets]
            [gdl.graphics :as g]
            [gdl.graphics.color :as color]
            [gdl.graphics.batch :refer [batch]]
            [gdl.graphics.unit-scale :refer [*unit-scale*]]
            [gdl.graphics.world :as world]
            [gdl.graphics.gui :as gui])
  (:import com.badlogic.gdx.graphics.g2d.TextureRegion))

; Explanation why not using libgdx Sprite class:
; * mutable fields
; * render in certain position/scale -> the sprite is modified somewhere else !
; * would have to reset it after every render ... or copy ?...
; * -> I cache only dimensions & scale for my texture-regions
; * color & rotation applied on rendering

; TODO one 'draw' with options scale,rotation,color,etc.

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
  (if color (.setColor batch color/white)))

(defn- unit-dimensions [image]
  {:pre [(bound? #'*unit-scale*)]}

  ; TODO :
  ; * unit-scale is either :world-units or :pixels
  ; :wu or :px
  ; !

  (cond
   (= *unit-scale* world/unit-scale) (:world-unit-dimensions  image)
   (= *unit-scale* gui/unit-scale)   (:pixel-dimensions       image)))

(defn draw
  ([{:keys [texture color] :as image} position]
   (draw-texture texture position (unit-dimensions image) 0 color))
  ([image x y]
   (draw image [x y])))

(defn draw-rotated-centered
  [{:keys [texture color] :as image} rotation [x y]]
  (let [[w h] (unit-dimensions image)]
    (draw-texture texture
                  [(- x (/ w 2))
                   (- y (/ h 2))]
                  [w h]
                  rotation
                  color)))

(defn draw-centered [image position]
  (draw-rotated-centered image 0 position))

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
  ; TODO here implicit assumption gui-unit-scale = 1 ...
  ; nope ! pixel-unit-scale is 1 !!!
  (let [pixel-dimensions (if (number? scale)
                           (mapv (partial * scale) (texture-dimensions texture))
                           scale)]
    (assoc image
           :pixel-dimensions pixel-dimensions
           :world-unit-dimensions (mapv (partial * world/unit-scale) pixel-dimensions))))

(defrecord Image [file ; -> is in texture data, can remove.
                  texture ; -region ?
                  sub-image-bounds ; => is in texture-region data?
                  scale

                  pixel-dimensions
                  world-unit-dimensions

                  tilew
                  tileh])

(defn- get-texture-region [file & [x y w h]]
  (let [texture (assets/get-texture file)]
    (if (and x y w h)
      (TextureRegion. texture (int x) (int y) (int w) (int h))
      (TextureRegion. texture))))

(defn create
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
  (assoc (create file) :tilew tilew :tileh tileh))

(defn get-sprite [{:keys [tilew tileh] :as sheet} [x y]]
  (get-sub-image sheet (* x tilew) (* y tileh) tilew tileh))

(defn get-sheet-frames [sheet]
  (let [[w h] (:pixel-dimensions sheet)]
    (for [y (range (/ w (:tilew sheet)))
          x (range (/ h (:tileh sheet)))]
      (get-sprite sheet [x y]))))

(defn spritesheet-frames [& args]
  (get-sheet-frames (apply spritesheet args)))
