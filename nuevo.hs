---------------------------------------------------------------------------------
-- Proyecto 2: Grafos Notables
-- Lenguaje: Haskell
-- Asignatura: Lenguajes de Programación
--
-- Estudiante: Asencion Gonzalez
-- Cedula:31.502.822
-- Email: gaasencion5@gmail.com
---------------------------------------------------------------------------------

import Data.List (nub, sort, isPrefixOf)
import Data.Maybe (mapMaybe)
import qualified Data.Map as M
import qualified Data.Set as S
import Control.Monad (forM_) -- Para manejar la lectura del archivo

--------------------------------------------------------------------------------
-- 1. ESTRUCTURA DE DATOS (TIPOS)
--------------------------------------------------------------------------------

-- Define un Nodo como un entero (su etiqueta)
type Node = Int
-- Define una Arista como un par de Nodos (no dirigido)
type Edge = (Node, Node)

-- Define la estructura de Grafo
data Graph = Graph {
    vertices :: [Node],     -- Lista de vértices
    edges :: [Edge]         -- Lista de aristas
} deriving (Show, Eq)

-- Lista de Adyacencia: Mapa que asocia cada Nodo con la lista de sus vecinos
type AdjList = M.Map Node [Node]

-- Función auxiliar para construir la Lista de Adyacencia a partir del Grafo
buildAdjList :: Graph -> AdjList
buildAdjList g = foldl addEdge M.empty (edges g)
    where
        -- Función para insertar una arista (u,v) en el mapa de adyacencia
        addEdge acc (u, v)
            | u == v    = acc                                    -- Ignorar lazos en la adyacencia
            | otherwise = M.insertWith (++) u [v] (M.insertWith (++) v [u] acc)

--------------------------------------------------------------------------------
-- 2. PARSING (LECTURA DE ENTRADA)
--------------------------------------------------------------------------------

-- Nota: El parsing es el más complicado. Esta función simplifica la lectura
-- esperando un formato muy específico y usando pattern matching en strings.

-- parseLine :: String -> Graph
parseLine line =
    let 
        -- 1. Separar la línea en dos partes: Vértices (V) y Aristas (A)
        -- Ejemplo: "({1,2,3}, {(1,2),(2,3)})"
        -- Buscamos la división entre las dos tuplas respetando anidamiento
        inner = init . tail $ line -- elimina paréntesis exteriores
        (leftPart, rightPart) = splitTopComma inner
        parts = [trim leftPart, trim rightPart]

        -- 2. Extraer y limpiar Vértices (primera parte)
        -- Elimina '{' y '}' y convierte la lista de strings a una lista de Nodos (Int)
        v_str = filter (`notElem` "{ }") (head parts)
        v_list = if null (trim v_str) then [] else mapMaybe (maybeRead . trim) (splitOn ',' v_str) :: [Node]

        -- 3. Extraer y limpiar Aristas (segunda parte)
        a_str = filter (`notElem` "{ }") (parts !! 1)
        -- Si no hay aristas (por ejemplo "{}"), devolver lista vacía
        a_list = if null (trim a_str)
                 then []
                 else let a_str_no_space = filter (/= ' ') a_str
                          a_pairs_str = map trim $ filter (not . null) $ splitOnStr ")," a_str_no_space
                      in mapMaybe parsePairMaybe a_pairs_str
        
        -- Función auxiliar para parsear un par "(u,v"
        -- Safe parser for a pair; returns Nothing on parse failure
        parsePairMaybe :: String -> Maybe Edge
        parsePairMaybe s =
            let piece
                    | null s        = s
                    | head s /= '(' = '(' : s
                    | otherwise     = s
                inner = takeWhile (/= ')') (tail piece) -- elimina paréntesis finales si existen
                nums = mapMaybe (maybeRead . trim) (splitOn ',' inner)
            in case nums of
                [u, v] -> Just (u, v)
                _      -> Nothing
                
        -- a_list definido arriba (ya maneja aristas vacías)
        
    in 
        Graph (nub v_list) (normalizeEdges (nub a_list)) -- Usa nub para eliminar duplicados

-- Funciones auxiliares de parsing (simples versiones de string splitting)
splitOn :: Char -> String -> [String]
splitOn c s = 
    case break (==c) s of
        (chunk, []) -> [chunk]
        (chunk, rest) -> chunk : splitOn c (tail rest)

-- Split on a substring separator (simple implementation)
splitOnStr :: String -> String -> [String]
splitOnStr sep s
    | null sep  = error "splitOnStr: empty separator"
    | otherwise = go s
  where
    go "" = [""]
    go str
        | sep `isPrefixOf` str = "" : go (drop (length sep) str)
        | otherwise = let (c:cs) = str
                          (x:xs) = go cs
                      in (c:x):xs

-- Split a string at the top-level comma (not inside braces/parentheses)
splitTopComma :: String -> (String, String)
splitTopComma = go 0 []
    where
        go _ acc "" = (reverse acc, "")
        go lvl acc (c:cs)
                | c == '{' || c == '(' = go (lvl + 1) (c:acc) cs
                | c == '}' || c == ')' = go (lvl - 1) (c:acc) cs
                | c == ',' && lvl == 0  = (reverse acc, cs)
                | otherwise             = go lvl (c:acc) cs

trim :: String -> String
trim = f . f
    where f = reverse . dropWhile (`elem` " \t\n\r")

-- Safe read: devuelve `Just a` si `s` se parsea completamente como tipo Read a
maybeRead :: Read a => String -> Maybe a
maybeRead s =
    case reads s of
        [(x, rest)] | trim rest == "" -> Just x
        _ -> Nothing

-- Normaliza (u,v) para que siempre u <= v y evitar (1,2) y (2,1) como aristas separadas
normalizeEdges :: [Edge] -> [Edge]
normalizeEdges = map (\(u,v) -> if u > v then (v,u) else (u,v))

--------------------------------------------------------------------------------
-- 3. LÓGICA DE GRAFOS NOTABLES (Funciones Puras)
--------------------------------------------------------------------------------

-- Función de alto nivel para ejecutar todas las verificaciones
checkAllProperties :: Graph -> [String]
checkAllProperties g = 
    -- Usa un "do-block" de lista para verificar y construir la lista de resultados
    [ "Grafo Nulo"                | isNullGraph g ]
    ++ [ "Grafo Vacio"            | isEmptyGraph g ]
    ++ [ "Grafo Unitario"         | isUnitaryGraph g ]
    ++ [ "Grafo Simple"           | isSimpleGraph g ]
    ++ [ "Grafo Conexo"           | isConnectedGraph g ]
    ++ [ "Grafo Completo"         | isCompleteGraph g ]
    ++ [ "Grafo Bipartido"        | isBipartiteGraph g ]
    -- Nota: isCompleteBipartite requiere más lógica, simplificado por ahora
    -- ++ [ "Grafo Bipartido Completo" | isCompleteBipartite g ] 
    ++ [ "Arbol"                  | isTree g ]
    ++ [ "Grafo Euleriano"        | isEulerian g ]
    ++ [ "Grafo Plano"            | isPlanar g ]


-- A. Verificaciones Básicas
isNullGraph :: Graph -> Bool
isNullGraph g = null (vertices g)

isEmptyGraph :: Graph -> Bool
isEmptyGraph g = null (edges g)

isUnitaryGraph :: Graph -> Bool
isUnitaryGraph g = length (vertices g) == 1 && isSimpleGraph g

isSimpleGraph :: Graph -> Bool
isSimpleGraph g = all (uncurry (/=)) (edges g)


-- B. Grados y Adyacencia
getDegree :: Node -> AdjList -> Int
getDegree node adjList = length (M.findWithDefault [] node adjList)

-- C. Conectividad (DFS/BFS - Depth First Search)
-- Usa un Set para mantener los nodos visitados
isConnectedGraph :: Graph -> Bool
isConnectedGraph g
    | isNullGraph g = True
    | otherwise =
        let
            adj = buildAdjList g
            startNode = head (vertices g)
            -- DFS recursivo para marcar nodos visitados
            dfs visited node = 
                let 
                    neighbors = M.findWithDefault [] node adj
                    unvisited = filter (`S.notMember` visited) neighbors
                in 
                    foldl dfs (S.insert node visited) unvisited
            
            visitedSet = dfs S.empty startNode
        in
            -- Es conexo si el número de nodos visitados es igual al total de vértices
            S.size visitedSet == length (vertices g)


-- D. Grafo Completo
isCompleteGraph :: Graph -> Bool
isCompleteGraph g
    | not (isSimpleGraph g) = False
    | otherwise =
        let 
            n = length (vertices g)
            maxEdges = (n * (n - 1)) `div` 2
        in
            length (edges g) == maxEdges


-- E. Grafo Bipartido (Coloración 2-Colores)
isBipartiteGraph :: Graph -> Bool
isBipartiteGraph g
    | isNullGraph g = True
    | otherwise =
        let
            adj = buildAdjList g
            -- Map: Node -> Maybe Int (Nothing: sin color, Just 1: Color A, Just -1: Color B)
            coloring = M.fromList [(v, Nothing) | v <- vertices g]
            
            -- Función recursiva para colorear/verificar la componente
            colorComponent :: Node -> Int -> M.Map Node (Maybe Int) -> Maybe (M.Map Node (Maybe Int))
            colorComponent u color map = 
                case M.lookup u map of
                    Just Nothing -> 
                        let newMap = M.insert u (Just color) map
                        in foldr (\v acc -> 
                            case acc of 
                                Nothing -> Nothing -- Propagación de fallo
                                Just m -> colorComponent v (-color) m) 
                            (Just newMap) (M.findWithDefault [] u adj)
                    
                    Just (Just c)
                        | c == color -> Just map -- Ya coloreado correctamente
                        | otherwise  -> Nothing   -- Falla: Colores opuestos adyacentes
                    
                    Nothing -> Just map -- Nodo no existe, se ignora
            
            -- Itera sobre todos los nodos para manejar componentes desconectadas
            tryColoring map [] = Just map
            tryColoring map (u:rest) = 
                case M.lookup u map of
                    Just Nothing -> -- Nodo sin colorear
                        case colorComponent u 1 map of
                            Nothing -> Nothing -- Falló en esta componente
                            Just m  -> tryColoring m rest
                    _ -> tryColoring map rest -- Nodo ya coloreado o no existe
                    
        in
            case tryColoring coloring (vertices g) of
                Just _ -> True
                Nothing -> False


-- F. Árbol
isTree :: Graph -> Bool
isTree g 
    | isNullGraph g = False -- O True, según convención. Aquí asumimos V>=1
    | otherwise = isConnectedGraph g && length (edges g) == length (vertices g) - 1


-- G. Euleriano
isEulerian :: Graph -> Bool
isEulerian g
    | not (isConnectedGraph g) && not (null (edges g)) = False
    | otherwise =
        let
            adj = buildAdjList g
            degrees = map (`getDegree` adj) (vertices g)
            oddDegrees = filter odd degrees
        in
            -- Permite 0 (Ciclo Euleriano) o 2 (Camino Euleriano)
            length oddDegrees <= 2


-- H. Plano (Heurística de Euler)
isPlanar :: Graph -> Bool
isPlanar g
    | length (vertices g) <= 2 = True
    | otherwise = length (edges g) <= 3 * length (vertices g) - 6

--------------------------------------------------------------------------------
-- 4. FUNCIÓN MAIN (MANEJO DE ARCHIVOS)
--------------------------------------------------------------------------------

main :: IO ()
main = do
    -- Lectura del archivo data.io
    content <- readFile "data.io"
    let linesOfFile = lines content
    
    -- Procesar cada línea y generar salida
    forM_ (zip [1..] linesOfFile) $ \(i, line) -> do
        let tline = trim line
        -- Ignorar líneas vacías o comentarios (comienzan con "--")
        if null tline || isPrefixOf "--" tline
            then return ()
            else do
                let g = parseLine line
                let results = checkAllProperties g
                
                putStr $ "Caso " ++ show i ++ ": "
                if null results
                    then putStrLn "Ninguna propiedad notable detectada"
                    else putStrLn (formatResults results)

    where
        -- Función auxiliar para imprimir resultados separados por coma
        formatResults [] = ""
        formatResults [r] = r
        formatResults (r:rs) = r ++ ", " ++ formatResults rs