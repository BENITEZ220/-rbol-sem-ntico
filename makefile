# Directorios de origen y destino
SRC_DIR := src
BIN_DIR := bin
INCLUDE_DIR := include

# Archivos fuente y ejecutable
CPP_FILES := $(wildcard $(SRC_DIR)/*.cpp)
EXECUTABLE := $(BIN_DIR)/main

# Librerías SFML
SFML := -lsfml-graphics -lsfml-window -lsfml-system -lsfml-audio

# Regla para compilar el ejecutable principal
$(EXECUTABLE): $(CPP_FILES)
	g++ $(CPP_FILES) -o $(EXECUTABLE) $(SFML) -I$(INCLUDE_DIR) -std=c++17

# Regla por defecto para compilar el proyecto
all: $(EXECUTABLE)

# Regla para ejecutar el programa
run: $(EXECUTABLE)
	./$(EXECUTABLE)

# Regla para compilar y ejecutar el programa
main: all
	./$(EXECUTABLE)

# Regla para limpiar los archivos generados
clean:
	if exist "$(EXECUTABLE)" del /Q "$(EXECUTABLE)"

.PHONY: all clean run