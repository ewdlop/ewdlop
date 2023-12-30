(function(){
    let canvas = document.getElementById('myCanvas');
    let ctx = canvas.getContext('2d');
    
    // Define the size of the game board
    let rows = 500;
    let cols = 500;
    
    // Initialize the grid and fill with random life forms
    let grid = create2DArray(rows, cols);
    
    // sample 2D array creation function
    function create2DArray(rows, cols) {
        let arr = new Array(rows);
        for (var i = 0; i < arr.length; i++) {
            arr[i] = new Array(cols).fill(0).map(() => Math.floor(Math.random() * 2));
        }
        return arr;
    }
    
    // Count the number of live neighbors for a given cell
    function countLiveNeighbors(grid, x, y) {
        let count = 0;
        // Define the directions of all 8 neighbors
        let directions = [
            [-1, -1], [-1, 0], [-1, 1],
            [0, -1], /*[0,0],*/ [0, 1],
            [1, -1], [1, 0], [1, 1]
        ];
    
        // Check each neighbor
        for (let i = 0; i < directions.length; i++) {
            let dir = directions[i];
            let newX = x + dir[0];
            let newY = y + dir[1];
    
            // Check the bounds and then check if neighbor is alive
            if (newX >= 0 && newX < grid.length && newY >= 0 && newY < grid[0].length) {
                count += grid[newX][newY];
            }
        }
    
        return count;
    }
    
    // Update the grid based on the rules of Conway's Game of Life
    function updateGrid(grid) {
        let newGrid = create2DArray(grid.length, grid[0].length);
    
        // Apply the rules to each cell in the grid
        for (let i = 0; i < grid.length; i++) {
            for (let j = 0; j < grid[i].length; j++) {
                let liveNeighbors = countLiveNeighbors(grid, i, j);
    
                if (grid[i][j] === 1) { // Cell is alive
                    if (liveNeighbors < 2 || liveNeighbors > 3) {
                        newGrid[i][j] = 0; // Cell dies
                    } else {
                        newGrid[i][j] = 1; // Cell stays alive
                    }
                } else { // Cell is dead
                    if (liveNeighbors === 3) {
                        newGrid[i][j] = 1; // Cell becomes alive
                    } else {
                        newGrid[i][j] = 0; // Cell stays dead
                    }
                }
            }
        }
    
        return newGrid;
    }
    
    // Function to resize the canvas to full screen
    function resizeCanvas() {
        canvas.width = window.innerWidth;
        canvas.height = window.innerHeight;
    }
    
    // Function to draw on the canvas (example content)
    function drawGrid() {
        ctx.clearRect(0, 0, canvas.width, canvas.height);
        for (var i = 0; i < rows; i++) {
            for (var j = 0; j < cols; j++) {
                if(grid[i][j] === 1) {
                    width = canvas.width/rows;
                    height = canvas.height/cols;
                    ctx.fillStyle = "black";
                    ctx.fillRect(j * width, i * height, width, height); // Adjust size as needed
                }
            }
        }
    }
    
    // Call resizeCanvas initially and on every window resize
    function drawScene(){
        grid = updateGrid(grid);
        drawGrid();
        requestAnimationFrame(drawScene);
    }
    
    
    
    window.addEventListener('resize', resizeCanvas, false);
    resizeCanvas();
    drawScene();
})();



