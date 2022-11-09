(ns engine.tiled
  (:require [data.grid2d :as grid])
  (:import [com.badlogic.gdx.maps MapLayers]
           [com.badlogic.gdx.maps.tiled TmxMapLoader TiledMap TiledMapTile
            TiledMapTileLayer TiledMapTileLayer$Cell]
           [com.badlogic.gdx.maps.tiled.tiles StaticTiledMapTile]))

(defn load-map
  "Requires OpenGL context (texture generation)."
  [file]
  (.load (TmxMapLoader.) file))

(defn dispose [tiled-map]
  (.dispose tiled-map))

(defmulti ^:private get-property (fn [obj k] (class obj)))

(defmethod get-property TiledMap [^TiledMap tiled-map k]
  (.get (.getProperties tiled-map) (name k)))

(defmethod get-property TiledMapTile [^TiledMapTile tile k]
  (.get (.getProperties tile) (name k)))

(defn- ^MapLayers layers [tiled-map]
  (.getLayers ^TiledMap tiled-map))

(defn layer-index [tiled-map layer]
  (let [idx (.getIndex (layers tiled-map) (name layer))]
    (if-not (= -1 idx) idx)))

(defn- ^TiledMapTileLayer$Cell cell-at [[x y] tiled-map layer]
  (if-let [layer (.get (layers tiled-map) (name layer))]
    (.getCell ^TiledMapTileLayer layer x y)))

(defn property-value [position tiled-map layer property]
  {:pre [(keyword? property)]}
  (if-let [cell (cell-at position tiled-map layer)]
    (if-let [value (get-property (.getTile cell) property)]
      value
      :undefined)
    :no-cell))

(defn width [tiled-map]
  (get-property tiled-map :width))

(defn height [tiled-map]
  (get-property tiled-map :height))

(defn positions-with-property [tiled-map layer property]
  (if (layer-index tiled-map layer)
    (for [x (range (width tiled-map))
          y (range (height tiled-map))
          :let [position [x y]
                value (property-value position tiled-map layer property)]
          :when (not (#{:undefined :no-cell} value))]
      [position value])))

(defn- properties [obj]
  (let [ps (.getProperties obj)]
    (zipmap (map keyword (.getKeys ps)) (.getValues ps))))

(defn- tilesets [tiled-map]
  (map (fn [tileset]
         {:name (.getName tileset)
          :size (.size tileset)
          :properties (properties tileset)})
       (.getTileSets tiled-map)))

; Useful for calculating new localids after increasing spritesheets width
; increase spritesheet width from 4 to 7 and update localids:
; (convert-to-localid (convert-to-spriteposi localid 4) 7)
#_(defn- convert-to-localid [[x y] sheetw]
    (+ x (* y sheetw)))

(defn convert-to-spriteposi [localid sheetw]
  {:post [(integer? (% 0))
          (integer? (% 1))]}
  (assert (and (integer? localid) (>= localid 0)) (str "localid: " localid))
  [(mod localid sheetw)
   (int (/ localid sheetw))])

(defn- firstgid [tileset]
  (:firstgid (:properties tileset)))

(defn- tile->tileset [tiled-map ^TiledMapTile tile]
  (let [gid (.getId tile)
        tilesets (tilesets tiled-map)]
    (apply max-key firstgid
           (filter #(>= gid (firstgid %)) tilesets))))

(defn- tileset-width [tileset]
  (/ (:imagewidth (:properties tileset))
     (:tilewidth (:properties tileset))))

(defn get-spriteidx [position tiled-map layer]
  (if-let [cell (cell-at position tiled-map layer)]
    (let [tile (.getTile cell)
          tileset (tile->tileset tiled-map tile)
          gid (.getId tile)]
      (convert-to-spriteposi (- gid (firstgid tileset))
                             (tileset-width tileset)))))

(defn- make-layer [layer-name cell-grid sprite-sheet get-sprite sprite-posi-key]
  (let [layer (TiledMapTileLayer. (grid/width cell-grid)
                                  (grid/height cell-grid)
                                  (:tilew sprite-sheet)
                                  (:tileh sprite-sheet))
        texture->tile (memoize (fn [texture] (StaticTiledMapTile. texture)))]
    (.setName layer layer-name)
    (doseq [[x y] (grid/posis cell-grid)
            :let [cell-grid-cell (get cell-grid [x y])]
            :when cell-grid-cell]
      (if-let [sprite-idx (sprite-posi-key @cell-grid-cell)]
        (let [cell (TiledMapTileLayer$Cell.)]
          (.setTile cell (texture->tile
                          (:texture
                           (get-sprite sprite-sheet sprite-idx))))
          (.setCell layer x y cell))))
    layer))

(comment

 make-tiled-map
 :width
 :height
 :tile-width
 :tile-height
 :layers [{:name
           :position->texture-region}]

 ; :position->texture-region
 ; should return same texture-region objects if it is the same value
 ; as then the tiles will be re-used

 )

(defn make-tiled-map
  [cell-grid sprite-sheet details-sprite-sheet get-sprite]
  (let [tiled-map (TiledMap.)
        layers (layers tiled-map)]
    (.add layers (make-layer "ground"
                             cell-grid
                             sprite-sheet
                             get-sprite
                             :sprite-posi))
    (if details-sprite-sheet
      (.add layers (make-layer "details"
                               cell-grid
                               details-sprite-sheet
                               get-sprite
                               :details-sprite-posi)))
    tiled-map))

(comment

 (def tm
   (:tiled-map
    (:tech-graveyard (deref (var game.maps.data/maps-data)))))

 (.getTile (cell-at [26 57] tm "ground"))

 )
