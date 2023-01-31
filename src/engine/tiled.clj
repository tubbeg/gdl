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

(defn property-value
  "Returns the property value from layer and position.
  If there is no cell returns :no-cell and if the property value is undefined returns :undefined."
  [position tiled-map layer property]
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

;; Programmatic creation of tiled-maps from a combination of tiled-maps on a grid

; No copied-tile for AnimatedTiledMapTile yet (there was no generic copy)
(defn- make-layer [grid layer-name tilewidth tileheight]
  (let [layer (TiledMapTileLayer. (grid/width grid)
                                  (grid/height grid)
                                  tilewidth
                                  tileheight)]
    (.setName layer layer-name)
    (doseq [[x y] (posis grid)
            :let [{:keys [local-position tiled-map]} (get grid [x y])]
            :when local-position]
      (if local-position
        (if-let [cell (cell-at local-position tiled-map layer-name)]
          (let [new-cell (TiledMapTileLayer$Cell.)
                copied-tile (StaticTiledMapTile. ^StaticTiledMapTile
                                                 (.getTile cell))]
            ; TODO could cache tiles with same texture (or same getTile result, which is already cached ?)
            ; local-tile (.getTile cell)
            ; copied-tile (memoize (fn [tile]  (StaticTiledMapTile. ^StaticTiledMapTile local-tile)))
            (.setTile new-cell copied-tile)
            (.setCell layer x y new-cell)))
        ; TODO else case
        ; - only for ground layer -
        ; no tile at position
        ; check if is adjacent to any tile
        ; -> then its a wall
        ; -> us wall placement function
        ))
    layer))

(defn make-tiled-map
  "Grid cells can have :local-position and :tiled-map keys."
  [grid]
  (let [tiled-map (TiledMap.)
        properties (.getProperties tiled-map)
        _ (.put properties "width" (grid/width grid))
        _ (.put properties "height" (grid/height grid))
        layers (layers tiled-map)
        module-tiled-map (:tiled-map (first (filter :tiled-map (grid/cells grid))))
        tilewidth (get-property module-tiled-map :tilewidth)
        tileheight (get-property module-tiled-map :tileheight)
        layer-names (map (memfn getName) (layers module-tiled-map))]
    (doseq [layer-name layer-names]
      (.add layers (make-layer grid layer-name tilewidth tileheight)))
    tiled-map))
